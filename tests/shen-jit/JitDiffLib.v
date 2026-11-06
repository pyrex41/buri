(* Differential harness for rocq/JitBytecode.v: runs generated cases and compares the
   canonical text of each result with what the pinned binary did. Test evidence only. *)
From Coq Require Import List ZArith NArith PArith Bool String Ascii.
From Buri Require Import JitFloat JitBytecode.
Import ListNotations.
Module JitDiffLib.
Import JitFloat.JitFloat JitBytecode.JitBytecode.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.

Definition hex_digit (n : N) : N := if N.ltb n 10 then 48 + n else 87 + n.
Fixpoint hex (s : text) : text := match s with
 | [] => [] | b :: r => hex_digit (N.shiftr b 4) :: hex_digit (N.land b 15) :: hex r end.
Fixpoint canon (h : tree obj) (d : nat) {struct d} : val -> text := match d with
 | O => fun _ => t "#"
 | S d' => fix go (v : val) : text := match v with
   | VPair a x => t "(" ++ canon h d' a ++ t " " ++ go x ++ t ")"
   | VFix z => t "n" ++ z_text z
   | VReal b => t "n" ++ format_real b
   | VPvar o => t "V" ++ z_digits o
   | VStr s => [34] ++ hex s ++ [34]
   | VBool true => t "T" | VBool false => t "F" | VNil => t "N"
   | VSym s => t "s" ++ hex (text_of_sym s)
   | VVec l => t "[" ++ flat_map (fun c => canon h d' c ++ t " ")
                          (match tget l h with Some (OVec c) => c | _ => [] end) ++ t "]"
   | VBytes _ => t "B"
   | x => to_string_atom x end end.

(* Case results. *)
Inductive outcome := DOk (s : text) | DErr (msg : text) | DStuck (why : stuck) | DIO | DFuel.
Definition env0 : env := Env (fun _ => false)
  (fun top => N.ltb 134217728 top) (fun _ => 0%Z).

Definition ptab := prim_tree.
Fixpoint steps (pt : tree (prim * nat)) (f : nat) (m : machine) : sum machine (result) := match f with
 | O => inl m
 | S f => match next env0 pt m with
   | MTau m' => steps pt f m'
   | MIO _ _ => inr RNeedsIO
   | MFinal o m' => inr (RDone o m')
   | MStuck w => inr (RStuck w) end end.
Fixpoint chunks (pt : tree (prim * nat)) (n : nat) (m : machine) : result := match n with
 | O => ROutOfFuel
 | S n => match steps pt 4096 m with
   | inl m' => chunks pt n m'
   | inr r => r end end.
Definition run_move (pt : tree (prim * nat)) (mv : move) : result := match mv with
 | MTau m => chunks pt 8192 m
 | MIO _ _ => RNeedsIO | MFinal o m => RDone o m | MStuck w => RStuck w end.

(* The install primitive, run the way (shen-jit.install L) is. *)
Definition installer (form : val) : code :=
 Code (VSym (sym "boot")) 0 None 3 [form] [IPrim 2 PInstall [OConst 0]; IReturn (OSlot 2)] [] VNil.
Definition run_install (pt : tree (prim * nat)) (m : machine) (form : val) : result :=
 let c := installer form in
 chunks pt 4 (set_ctl (set_handlers m []) (tset (skey 1) VNil Leaf) 0 c (code_ins c) []).

Definition exn_text (m : machine) (e : val) : text := match e with
 | VExn l => match tget l (m_heap m) with
   | Some (OExn msg v) => exception_text (m_heap m) msg v | _ => t "?" end
 | _ => t "?" end.

Definition is_defun (form : val) : bool := match form with
 | VPair (VSym h) _ => Pos.eqb h (sym "defun") | _ => false end.
Definition rest_of (r : result) (m : machine) : machine := match r with RDone _ m' => m' | _ => m end.
Definition report (r : result) : outcome := match r with
 | RDone (FReturn v) m => DOk (canon (m_heap m) 64 v)
 | RDone (FError e) m => DErr (exn_text m e)
 | RDone (FExit z) _ => DOk (t "exit" ++ z_text z)
 | RStuck w => DStuck w | RNeedsIO => DIO | ROutOfFuel => DFuel end.
Definition run_case (pt : tree (prim * nat)) (m : machine) (form : val) : outcome * machine :=
 let r := run_install pt m form in
 if is_defun form then (report r, rest_of r m)
 else match r with
   | RDone (FReturn v) m1 =>
     let r2 := run_move pt (start env0 m1 v) in (report r2, rest_of r2 m1)
   | _ => (report r, rest_of r m) end.

Inductive verdict := VAgree | VDiff (got : outcome) | VNo (got : outcome).
Definition judge (o : outcome) (ok : bool) (exp : text) : verdict := match o with
 | DOk s => if (ok && text_eqb s exp)%bool then VAgree else VDiff o
 | DErr s => if (negb ok && text_eqb (hex s) exp)%bool then VAgree else VDiff o
 | _ => VNo o end.

Fixpoint run_all (pt : tree (prim * nat)) (m : machine) (cs : list (val * bool * string)) : list verdict :=
 match cs with
 | [] => []
 | (form, ok, exp) :: r =>
   let '(o, m') := run_case pt m form in
   judge o ok (t exp) :: run_all pt m' r end.

(* Preload definitions, sealed, as stage 0 does; then globals. *)
Fixpoint preload (pt : tree (prim * nat)) (m : machine) (fs : list val) : machine := match fs with
 | [] => m
 | f :: r => preload pt (rest_of (run_install pt m f) m) r end.
Definition sealing_on (m : machine) := set_globals m (m_gval m) (m_gfun m) (m_sealed m) true.
Definition sealing_off (m : machine) := set_globals m (m_gval m) (m_gfun m) (m_sealed m) false.
Fixpoint bytes_of_hex (l : list N) : list N := match l with
 | a :: b :: r =>
   let d c := if N.ltb c 58 then c - 48 else c - 87 in (16 * d a + d b) :: bytes_of_hex r
 | _ => [] end.
(* What sj_init_host gives every run: the standard streams and *home-directory*. *)
Definition with_std (m : machine) : machine :=
 let '(l0, m) := alloc m (OStream 0 SIn true) in
 let '(l1, m) := alloc m (OStream 1 SOut true) in
 let '(l2, m) := alloc m (OStream 2 SOut true) in
 set_globals m
   (tset (sym "*home-directory*") (VStr [])
   (tset (sym "*sterror*") (VStream l2)
   (tset (sym "*stoutput*") (VStream l1)
   (tset (sym "*stinput*") (VStream l0) (m_gval m)))))
   (m_gfun m) (m_sealed m) (m_seal_user m).
Definition seal_names (m : machine) (ns : list string) : machine :=
 set_globals m (m_gval m) (m_gfun m)
   (fold_left (fun tr n => tset (sym_of_text (bytes_of_hex (t n))) tt tr) ns (m_sealed m)) (m_seal_user m).
Definition set_gvals (m : machine) (gs : list (string * val)) : machine :=
 set_globals m (fold_left (fun tr g => tset (sym_of_text (t (fst g))) (snd g) tr) gs (m_gval m))
   (m_gfun m) (m_sealed m) (m_seal_user m).

(* Short names for generated data. *)
Definition y (s : string) : val := VSym (sym s).
Definition st (s : string) : val := VStr (t s).
Definition sx (s : string) : val := VStr (bytes_of_hex (t s)).
Definition yx (s : string) : val := VSym (sym_of_text (bytes_of_hex (t s))).
Notation "a ;; b" := (VPair a b) (at level 60, right associativity).
Definition stuck_name (w : stuck) : string := match w with
 | RBadSlot _ => "bad-slot" | RBadConst => "bad-const" | RBadLabel => "bad-label" | RFallOff => "fall-off"
 | RBadCapture => "bad-capture" | RBadCode => "bad-code" | RIdentity => "identity" | RCyclic => "cyclic"
 | RExcluded _ => "excluded" | RArgs => "args" end.
Fixpoint to_str (l : list N) : string := match l with
 | [] => EmptyString | c :: r => String (ascii_of_N c) (to_str r) end.
Definition verdict_text (v : verdict) : string := match v with
 | VAgree => "agree"
 | VDiff (DOk s) => "diff-ok " ++ to_str s
 | VDiff (DErr s) => "diff-err " ++ to_str s
 | VDiff _ => "diff"
 | VNo (DStuck w) => "stuck " ++ stuck_name w
 | VNo DIO => "io" | VNo DFuel => "fuel" | VNo _ => "no" end.
End JitDiffLib.
