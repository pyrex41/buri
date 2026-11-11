(* Shen/JIT Phase 2, F00 and r1-share-ht: the share pass's checker, an instance of JitFrontCheck.fchk.
   lower.shen (934cfa5) `share` rewrites (if C X Y), where C is a chain of `and` tests and `let`
   bindings, to
       (let ElseN (freeze Y') (unchain C X' ElseN))
   where (unchain (and T S) Then G) = (if T (unchain S Then G) (thaw G)),
         (unchain (let V E S) Then G) = (let V E (unchain S Then G)),
         (unchain T Then G)           = (if T Then (thaw G)),
   and recurses into let bodies, do's second argument and if branches (the same-head case of fchk).
   In the then branch X' it reuses a chain variable bound to (hd V) or (tl V) for the same path
   (lower.shen's reuse/canon): (tl V) becomes the variable the chain bound to it.

   share_rule accepts (if C X Y) against (let G (freeze Y') U) when
   - G is not in the scope g and id_key is not in g (the target-only bindings G and the frozen
     closure's identity tag shadow nothing the source reads);
   - rec g Y Y';
   - chain_chk: U is C unchained, each test checked by rec in the chain's scope, each chain
     binder V outside g and different from G, every else branch exactly (thaw G) for this G, and
     the then branch checked by then_chk in the OUTER scope g, with the target facts the chain's
     lets of (hd y)/(tl y) recorded (chain_fact): a path fact (W, (X, ops)) says W holds X's value
     with hd/tl applied as ops, X a variable of g.
   then_chk accepts what rec accepts, a source path against a target variable whose fact is the
   same path over a variable of the scope (reuse_var), and the same named call or let with its
   parts checked again; a let of a reused path records the fact on both sides.
   share_rule_sound: the target's let, freeze and the push of the frozen closure take three target
   steps; the frozen closure's cell is target-only and lies outside the world (SRel_with_cell_tgt);
   each (thaw G) takes six target steps to reach Y' in the closure's environment, paid from the
   index (thaw_erel); the source's and/KAndR/if frames are related to the target's if frames
   frame by frame (kif_base, kand_frame); a chain let binds the same name on both sides
   (chain_let), and a chain let of a path steps both sides through the primitive call, so that
   the target's value is the path's (chain_let_path); the then branch is related by then_sound
   (the source re-evaluates a reused path silently, src_path, to a value related to the target
   variable's, VRel_pops).
   Premises (Section hypotheses of Share, each explicit in check_share_sound's statement):
   - HT: D defines thaw as the kernel does, (defun thaw (V) (V)): the thaw steps go through the
     store's thaw. Necessary: share_needs_thaw_outright (D_wf, FrontHyps and HP hold at D_hp, and
     share_rule is not rule_sound there). Not dischargeable for the pinned D on this back end:
     thaw's entry can only be the initial store's (thaw_stable, thaw_defun_refused), and with HT no
     store meeting D has Com (ht_not_com: Comp has no dynamic apply), so call_preservation_src's
     premises cannot all hold with it. Named residual: OB-JIT-SHARE-THAW.
   - HP: D holds hd and tl as the primitives, so that a reused path re-evaluated on the source
     gives the value the target's variable holds. Necessary, each half: share_needs_hd_tl (D_wf,
     FrontHyps and HT hold, D leaves hd or tl open, a store holds it as a user function with an
     effect, and share_rule is not rule_sound there). Any store with Com meets it (hp_of_com).
   HT, HP and D_wf hold together (share_premises_sat), so check_share_sound is not vacuous.
   - D_wf, for then_chk's named-call congruence (compat_call_core needs fund_below).
   FrontHyps is no premise: front_hyps derives it from D_wf.

   Stage 0: share_rewrites_validated (vm_compute) accepts the four definitions share rewrites at
   v0.6 (shen.macros, shen.process-let, shen.lambda-of-defun, shen.process-assoc); judge_share_sound
   turns acceptance into KRef under HT, HP and D_wf.

   Freshness: the checker tests the freshness facts it needs (G and the chain binders outside the
   scope, and from each other) directly; fresh_not_bound shows that fresh_ok's reserved-name
   premise implies them for the lowerer's names. no_keyword_binders is not used here: the checker
   reads Rocq's parse, where (thaw G) is a named call whatever binds what; it matters for parse
   fidelity (the binary reading the forms as Rocq does), which is call_preservation_src's premise. *)
From Coq Require Import List ZArith NArith PArith Bool String Ascii Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatCtl JitKRefCompatClo JitKRefFund JitFrontCheck JitLowerStage0.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontShare.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitKRef.JitKRef JitFrontCheck.JitFrontCheck.
Module KB := JitKRefBase.JitKRefBase.

Definition thaw_name : name := of_string "thaw".
Definition thaw_e (G : name) : expr := ECall thaw_name [EVar G].
Definition is_thaw_of (G : name) (e : expr) : bool := match e with
 | ECall t [EVar H] => text_eqb t thaw_name && text_eqb H G
 | _ => false end.

(* ---------- share's reuse: path facts and the then-branch checker ----------
   lower.shen's share reuses a variable the chain bound to (hd V) or (tl V) for the same hd/tl
   of the then branch (`canon`): the then branch reads, on the target, chain binders the source's
   then branch cannot see. A path (x, ops) is the variable x with hd (true) and tl (false) applied
   in order; a fact (y, p) says y's value is p's (FactsAll below). The chain records target facts
   for its lets of (hd y) or (tl y) (chain_fact); the then branch's own lets of a reused path record
   the fact on both sides; then_chk accepts a source path against a target variable whose fact is
   the same path over a variable of the common scope (reuse_var). Re-evaluating a path on the source
   gives the value the target's variable holds only if hd and tl are the primitives (Section
   hypothesis HP below). *)
Definition hd_name : name := of_string "hd".
Definition tl_name : name := of_string "tl".
(* D holds hd and tl as the primitives (HP) and nothing else: no thaw. *)
Definition D_hp : list (name * fundef) := [(hd_name, FPrim PHd); (tl_name, FPrim PTl)].
Definition path : Type := (name * list bool)%type.
Definition pop (o : bool) (v : value) : option value := match v with
 | VCons a d => Some (if o then a else d) | _ => None end.
Fixpoint pops (v : value) (ops : list bool) {struct ops} : option value := match ops with
 | [] => Some v | o :: ops => match pop o v with Some v' => pops v' ops | None => None end end.
Definition op_of (f : name) : option bool :=
 if text_eqb f hd_name then Some true else if text_eqb f tl_name then Some false else None.
Fixpoint path_of (e : expr) : option path := match e with
 | EVar x => Some (x, [])
 | ECall f [a] => match op_of f, path_of a with Some o, Some (x, ops) => Some (x, ops ++ [o]) | _, _ => None end
 | _ => None end.
Definition facts : Type := list (name * path).
Fixpoint flookup (y : name) (P : facts) : option path := match P with
 | [] => None | (z, p) :: P => if text_eqb y z then Some p else flookup y P end.
(* Drop the facts about x and the facts over x, when a let rebinds x. *)
Definition fdrop (x : name) (P : facts) : facts :=
 filter (fun q => negb (text_eqb (fst q) x) && negb (text_eqb (fst (snd q)) x)) P.
Definition canon (P : facts) (e : expr) : option path := match path_of e with
 | Some (x, ops) => match flookup x P with Some (b, ops0) => Some (b, ops0 ++ ops) | None => Some (x, ops) end
 | None => None end.
Definition path_eqb (p q : path) : bool := text_eqb (fst p) (fst q) && forall2b Bool.eqb (snd p) (snd q).

(* The source's path X against the target's variable X' = y: y's fact and X's canonical path are
   the same path, over a variable of the common scope g. *)
Definition reuse_path (g : list name) (Ps Pt : facts) (X X' : expr) : option path := match X' with
 | EVar y => match flookup y Pt, canon Ps X with
   | Some p, Some q => if path_eqb p q && bound g (fst p) then Some p else None
   | _, _ => None end
 | _ => None end.
Definition reuse_var (g : list name) (Ps Pt : facts) (X X' : expr) : bool :=
 match reuse_path g Ps Pt X X' with Some _ => true | None => false end.

(* The then branch: rec in the scope g (the source's then scope, bound on both sides), a reused
   path, or the same named call or let with the parts checked again. A let whose bound expression
   is a reused path records the fact on both sides, unless the path's base is the let's own name. *)
Fixpoint then_chk (rec : list name -> expr -> expr -> bool) (g : list name) (Ps Pt : facts) (X X' : expr) {struct X} : bool :=
 rec g X X' || reuse_var g Ps Pt X X' ||
 match X, X' with
 | ECall f l0, ECall f' l => text_eqb f f' && (fix go (l0 l : list expr) : bool := match l0, l with
     | [], [] => true | a :: l0, b :: l => then_chk rec g Ps Pt a b && go l0 l | _, _ => false end) l0 l
 | ELet x a b, ELet x' a' b' => text_eqb x x' &&
     (match reuse_path g Ps Pt a a' with
      | Some p => negb (text_eqb (fst p) x) && then_chk rec (x :: g) ((x, p) :: fdrop x Ps) ((x, p) :: fdrop x Pt) b b'
      | None => false end
      || (then_chk rec g Ps Pt a a' && then_chk rec (x :: g) (fdrop x Ps) (fdrop x Pt) b b'))
 | _, _ => false end.

(* The target fact a chain let (let x E ...) records: E is (hd y) or (tl y), the same on both
   sides, y in the chain's scope g, and y a variable of the then scope g0 or one with a fact. *)
Definition chain_fact (g g0 : list name) (Pt : facts) (x : name) (E E' : expr) : facts :=
 match E with
 | ECall f [EVar y] => match op_of f with
   | Some o => if expr_eqb E E' && bound g y then
       match flookup y Pt with
       | Some (b, ops) => (x, (b, ops ++ [o])) :: fdrop x Pt
       | None => if bound g0 y then (x, (y, [o])) :: fdrop x Pt else fdrop x Pt end
     else fdrop x Pt
   | None => fdrop x Pt end
 | _ => fdrop x Pt end.

(* U is the chain C unchained with then branch X (checked against the target's in scope g0, with
   the target facts Pt) and else label G; g is the chain's scope so far (g0 plus the chain binders). *)
Definition base_chk (rec : list name -> expr -> expr -> bool) (g0 : list name) (Pt : facts) (G : name) (X : expr)
  (g : list name) (C U : expr) : bool :=
 match U with
 | EIf T' X' Z => is_thaw_of G Z && rec g C T' && then_chk rec g0 [] Pt X X'
 | _ => false end.

Fixpoint chain_chk (rec : list name -> expr -> expr -> bool) (g0 : list name) (Pt : facts) (G : name) (X : expr)
  (g : list name) (C U : expr) {struct C} : bool :=
 base_chk rec g0 Pt G X g C U
 || match C, U with
 | EAnd T Sc, EIf T' U1 Z => is_thaw_of G Z && rec g T T' && chain_chk rec g0 Pt G X g Sc U1
 | ELet x E Sc, ELet x' E' U1 => text_eqb x x' && negb (bound g0 x) && negb (text_eqb x G) &&
     rec g E E' && chain_chk rec g0 (chain_fact g g0 Pt x E E') G X (x :: g) Sc U1
 | _, _ => false end.

Definition share_rule : rule := fun rec g e0 e => match e0, e with
 | EIf C X Y, ELet G (EFreeze Y') U =>
   negb (bound g G) && negb (bound g id_key) && rec g Y Y' && chain_chk rec g [] G X g C U
 | _, _ => false end.

Definition share_rules : list rule := [share_rule].

(* ---------- the checker over a definition ---------- *)
Fixpoint esize (e : expr) : nat := match e with
 | ELam _ b | EFreeze b | EType b | EDefun _ _ b => S (esize b)
 | ELet _ a b | EAnd a b | EOr a b | ETrap a b => S (esize a + esize b)
 | EIf c a b => S (esize c + esize a + esize b)
 | ECond l => S ((fix go (l : list (expr * expr)) : nat := match l with
     | [] => 0 | (c, b) :: l => esize c + esize b + go l end) l)
 | EApp h l => S (esize h + (fix go (l : list expr) : nat := match l with
     | [] => 0 | a :: l => esize a + go l end) l)
 | ECall _ l => S ((fix go (l : list expr) : nat := match l with
     | [] => 0 | a :: l => esize a + go l end) l)
 | _ => 1 end.

(* Every recursive call of fchk and of the share rule is on a strict part of the target, so the
   target's size is enough fuel. Fuel only bounds the search: soundness holds at every fuel. *)
Definition check_share (ps : list name) (b0 b : expr) : bool := fchk share_rules (S (esize b)) ps b0 b.

(* ---------- the share rule's decisions, by vm_compute ----------
   Over the parameter p: (if p 0 1) against
   - share_ok:   (let G (freeze 1) (if p 0 (thaw G)))   accepted, the rule's own shape;
   - share_swap: (let G (freeze 1) (if p (thaw G) 0))   rejected: then and else swapped;
   - share_thaw_other: (let G (freeze 1) (if p 0 (thaw p)))  rejected: the else thaws a variable
     that is not the ElseN the let binds.
   They come before every proof, so a mutant that changes one of these decisions fails here; the
   rejections come first, so a mutant that accepts a wrong shape fails at the rejection it breaks. *)
Definition sx_p : name := of_string "p".
Definition sx_G : name := of_string "G".
Definition share_src : expr := EIf (EVar sx_p) (ENum (NInt 0)) (ENum (NInt 1)).
Definition share_ok : expr := ELet sx_G (EFreeze (ENum (NInt 1))) (EIf (EVar sx_p) (ENum (NInt 0)) (thaw_e sx_G)).
Definition share_swap : expr := ELet sx_G (EFreeze (ENum (NInt 1))) (EIf (EVar sx_p) (thaw_e sx_G) (ENum (NInt 0))).
Definition share_thaw_other : expr := ELet sx_G (EFreeze (ENum (NInt 1))) (EIf (EVar sx_p) (ENum (NInt 0)) (thaw_e sx_p)).
Theorem share_rejects_swap : check_share [sx_p] share_src share_swap = false.
Proof. vm_compute. reflexivity. Qed.
Theorem share_rejects_thaw_other : check_share [sx_p] share_src share_thaw_other = false.
Proof. vm_compute. reflexivity. Qed.
Theorem share_accepts_basic : check_share [sx_p] share_src share_ok = true.
Proof. vm_compute. reflexivity. Qed.

(* Share's reuse, over the parameter V: (if (and (cons? V) (let S (tl V) (cons? S))) T 0) against
   (let G (freeze 0) (if (cons? V) (let S (tl V) (if (cons? S) S (thaw G))) (thaw G))):
   - reuse_ok:      T = (tl V), the path S was bound to: accepted (S reused for (tl V));
   - reuse_wrong_op: T = (hd V): rejected, S holds (tl V), not (hd V);
   - reuse_wrong_base: T = (tl W) for another parameter W: rejected, the same operation on another
     variable. Rejections first, so that a mutant that accepts a wrong path fails at the rejection. *)
Definition sx_V : name := of_string "V".
Definition sx_W : name := of_string "W".
Definition sx_S : name := of_string "S".
Definition consp (e : expr) : expr := ECall (of_string "cons?") [e].
Definition reuse_src (T : expr) : expr :=
 EIf (EAnd (consp (EVar sx_V)) (ELet sx_S (ECall tl_name [EVar sx_V]) (consp (EVar sx_S)))) T (ENum (NInt 0)).
Definition reuse_tgt : expr :=
 ELet sx_G (EFreeze (ENum (NInt 0))) (EIf (consp (EVar sx_V))
   (ELet sx_S (ECall tl_name [EVar sx_V]) (EIf (consp (EVar sx_S)) (EVar sx_S) (thaw_e sx_G))) (thaw_e sx_G)).
Theorem share_reuse_rejects_wrong_op : check_share [sx_V; sx_W] (reuse_src (ECall hd_name [EVar sx_V])) reuse_tgt = false.
Proof. vm_compute. reflexivity. Qed.
Theorem share_reuse_rejects_wrong_base : check_share [sx_V; sx_W] (reuse_src (ECall tl_name [EVar sx_W])) reuse_tgt = false.
Proof. vm_compute. reflexivity. Qed.
Theorem share_reuse_accepts : check_share [sx_V; sx_W] (reuse_src (ECall tl_name [EVar sx_V])) reuse_tgt = true.
Proof. vm_compute. reflexivity. Qed.

(* A rejection trace: the path of target constructors from the root to the deepest node where
   neither equality, the same head nor the share rule holds. Computed by Rocq, for the record of a
   rejection only; it decides nothing. *)
Local Open Scope string_scope.
Definition head (e : expr) : string := match e with
 | ENum _ => "num" | EStr _ => "str" | ESym _ => "sym" | EBool _ => "bool" | ENil => "nil"
 | EVar _ => "var" | ELam _ _ => "lambda" | ELet _ _ _ => "let" | EIf _ _ _ => "if"
 | EAnd _ _ => "and" | EOr _ _ => "or" | ECond _ => "cond" | ETrap _ _ => "trap"
 | EFreeze _ => "freeze" | EType _ => "type" | EDefun _ _ _ => "defun" | EApp _ _ => "app"
 | ECall _ _ => "call" end.

(* Why the share rule refuses a pair (if C X Y) / (let G (freeze Y') U): the first failing test. *)
Fixpoint chain_why (rec : list name -> expr -> expr -> bool) (g0 : list name) (Pt : facts) (G : name) (X : expr)
  (g : list name) (C U : expr) {struct C} : string :=
 let base := match U with
   | EIf T' X' Z =>
     if negb (is_thaw_of G Z) then "share: an else branch is not (thaw ElseN)"
     else if negb (rec g C T') then "share: a chain test differs"
     else if negb (then_chk rec g0 [] Pt X X') then "share: the then branch differs from the source's, reused paths included"
     else "share: base accepted"
   | _ => "share: not an unchained if" end in
 match C, U with
 | EAnd T Sc, EIf T' U1 Z =>
   if is_thaw_of G Z && rec g T T' then chain_why rec g0 Pt G X g Sc U1 else base
 | ELet x E Sc, ELet x' E' U1 =>
   if text_eqb x x' && negb (bound g0 x) && negb (text_eqb x G) && rec g E E'
   then chain_why rec g0 (chain_fact g g0 Pt x E E') G X (x :: g) Sc U1 else "share: a chain let differs, or binds a name of the scope or ElseN"
 | _, _ => base end.

Definition share_why (rec : list name -> expr -> expr -> bool) (g : list name) (e0 e : expr) : list string :=
 match e0, e with
 | EIf C X Y, ELet G (EFreeze Y') U =>
   [if bound g G then "share: ElseN is in scope"
    else if bound g id_key then "share: the identity key is in scope"
    else if negb (rec g Y Y') then "share: the frozen else differs from the source's"
    else chain_why rec g [] G X g C U]
 | _, _ => [] end.

Fixpoint share_trace (fuel : nat) (g : list name) (e0 e : expr) {struct fuel} : list string :=
 match fuel with
 | O => ["out of fuel"]
 | S f =>
   let ok := fchk share_rules fuel g e0 e in
   if ok then [] else
   let sub := match e0, e with
     | ELam x0 b0, ELam x b => if text_eqb x0 x then Some (x :: g, b0, b) else None
     | ELet x0 a0 b0, ELet x a b =>
       if text_eqb x0 x then
         if fchk share_rules f g a0 a then Some (x :: g, b0, b) else Some (g, a0, a)
       else None
     | EIf c0 a0 b0, EIf c a b =>
       if negb (fchk share_rules f g c0 c) then Some (g, c0, c)
       else if negb (fchk share_rules f g a0 a) then Some (g, a0, a) else Some (g, b0, b)
     | EAnd a0 b0, EAnd a b | EOr a0 b0, EOr a b | ETrap a0 b0, ETrap a b =>
       if fchk share_rules f g a0 a then Some (g, b0, b) else Some (g, a0, a)
     | EFreeze b0, EFreeze b | EType b0, EType b => Some (g, b0, b)
     | EIf _ _ Y, ELet G (EFreeze Y') _ =>
       if negb (bound g G) && negb (bound g id_key) && negb (fchk share_rules f g Y Y')
       then Some (g, Y, Y') else None
     | ECall f0 l0, ECall f1 l =>
       if text_eqb f0 f1 then
         (fix go (l0 l : list expr) : option (list name * expr * expr) := match l0, l with
          | a0 :: l0, a :: l => if fchk share_rules f g a0 a then go l0 l else Some (g, a0, a)
          | _, _ => None end) l0 l
       else None
     | EApp h0 l0, EApp h l =>
       if negb (fchk share_rules f g h0 h) then Some (g, h0, h) else
         (fix go (l0 l : list expr) : option (list name * expr * expr) := match l0, l with
          | a0 :: l0, a :: l => if fchk share_rules f g a0 a then go l0 l else Some (g, a0, a)
          | _, _ => None end) l0 l
     | _, _ => None end in
   match sub with
   | Some (g', a0, a) => (head e0 ++ "/" ++ head e) :: app (share_why (fchk share_rules f) g e0 e) (share_trace f g' a0 a)
   | None => (head e0 ++ "/" ++ head e ++ " rejected here") :: share_why (fchk share_rules f) g e0 e
   end
 end.

(* ---------- stage 0 data: forms against share witnesses ---------- *)
Import JitLowerStage0.JitLowerStage0.
Inductive sverdict := SAccepted (f : name) | SRejected (f : name) (trace : list string) | SUnparsed.

Definition judge_share (form share : sx) : sverdict :=
 match parse [] (to_value form), parse [] (to_value share) with
 | Some (EDefun f ps b0), Some (EDefun f' ps' b) =>
   if text_eqb f f' && forall2b text_eqb ps ps' then
     if check_share ps b0 b then SAccepted f else SRejected f (share_trace (S (esize b)) ps b0 b)
   else SUnparsed
 | _, _ => SUnparsed end.

Fixpoint judge_share_all (fs ss : list sx) : list sverdict := match fs, ss with
 | f :: fs, s :: ss => judge_share f s :: judge_share_all fs ss
 | [], [] => []
 | _, _ => [SUnparsed] end.

Definition show_name (t : name) : string :=
 String.string_of_list_ascii (map (fun n => Ascii.ascii_of_N n) t).

(* accepted, rejected, unparsed, and each rejection's name with its trace. *)
Definition tally_share (fs ss : list sx) : nat * nat * nat * list (string * list string) :=
 fold_right (fun v acc => let '(a, r, u, rs) := acc in match v with
   | SAccepted _ => (S a, r, u, rs)
   | SRejected f t => (a, S r, u, (show_name f, t) :: rs)
   | SUnparsed => (a, r, S u, rs) end) (0, 0, 0, [])%nat (judge_share_all fs ss).
(* The kernel's thaw, as stage 0 reads it (sys.forms, first line: (defun thaw (V3830) (V3830))), parses
   to the definition share_rule_sound's premise HT names, with tp = V3830: the premise can hold. *)
Definition kernel_thaw_form : sx := XList [XSym "defun"; XSym "thaw"; XList [XSym "V3830"]; XList [XSym "V3830"]].
Theorem kernel_thaw_parses : parse [] (to_value kernel_thaw_form) =
 Some (EDefun thaw_name [of_string "V3830"] (EApp (EVar (of_string "V3830")) [])).
Proof. vm_compute. reflexivity. Qed.

(* The four definitions of the pinned stage 0 (macros.forms lines 5, 9, 14 and 20) that share
   rewrites, with their share witnesses (the witness set of sha256 6881eb29..., macros.share at
   the same lines), as stage 0 prints them; generated by tests/shen-jit/stage0_to_rocq.py's
   tokenizer (its `rocq` function) from those two files. share_rewrites_validated: check_share
   accepts each, through share_rule with reuse (the pairs differ, so equality cannot). *)
Definition share_rewrite_forms : list sx := [(XList [(XSym "defun");(XSym "shen.macros");(XList [(XSym "V7180")]);(XList [(XSym "let");(XSym "GoTo7181");(XList [(XSym "freeze");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "V7180")]);(XList [(XSym "let");(XSym "Select7195");(XList [(XSym "hd");(XSym "V7180")]);(XList [(XSym "let");(XSym "Select7196");(XList [(XSym "tl");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "defmacro");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.process-def");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "defcc");(XSym "Select7195")]);(XList [(XSym "shen.yacc->shen");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "u!");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "cons");(XSym "protect");(XList [(XSym "cons");(XList [(XSym "shen.make-uppercase");(XList [(XSym "hd");(XSym "Select7196")])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "error");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "simple-error");(XList [(XSym "cons");(XList [(XSym "shen.mkstr");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "output");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "pr");(XList [(XSym "cons");(XList [(XSym "shen.mkstr");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stoutput");(XList [])]);(XList [])])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "pr");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "cons");(XSym "pr");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stoutput");(XList [])]);(XList [])])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "make-string");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.mkstr");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "lineread");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "lineread");(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stinput");(XList [])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "input");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "input");(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stinput");(XList [])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "read");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "read");(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stinput");(XList [])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "input+");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.process-input+");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "read-byte");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "shen.process-read-byte")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "prolog?");(XSym "Select7195")]);(XList [(XSym "shen.call-prolog");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "defprolog");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.compile-prolog");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "datatype");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.process-datatype");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "@s");(XSym "Select7195")]);(XList [(XSym "shen.process-@s");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "synonyms");(XSym "Select7195")]);(XList [(XSym "shen.process-synonyms");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "nl");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "nl");(XList [(XSym "cons");(XInt (1));(XList [])])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "let");(XSym "Select7195")]);(XList [(XSym "shen.process-let");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "/.");(XSym "Select7195")]);(XList [(XSym "shen.process-lambda");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "cases");(XSym "Select7195")]);(XList [(XSym "shen.process-cases");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "time");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "shen.process-time");(XList [(XSym "hd");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "put");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7182");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7182")]);(XList [(XSym "let");(XSym "Select7184");(XList [(XSym "tl");(XSym "Select7182")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7184")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7184")])])])])])])])]);(XList [(XSym "let");(XSym "Select7183");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "cons");(XSym "put");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7183")]);(XList [(XSym "cons");(XList [(XSym "hd");(XList [(XSym "tl");(XSym "Select7183")])]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "value");(XList [(XSym "cons");(XSym "*property-vector*");(XList [])])]);(XList [])])])])])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "get");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7185");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7185")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7185")])])])])])]);(XList [(XSym "cons");(XSym "get");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "hd");(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "value");(XList [(XSym "cons");(XSym "*property-vector*");(XList [])])]);(XList [])])])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "unput");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7186");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7186")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7186")])])])])])]);(XList [(XSym "cons");(XSym "unput");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "hd");(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "value");(XList [(XSym "cons");(XSym "*property-vector*");(XList [])])]);(XList [])])])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "shen.@c");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "shen.rcons_form");(XList [(XSym "hd");(XSym "Select7196")])]);(XList [(XSym "let");(XSym "GoTo7188");(XList [(XSym "freeze");(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7187");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7187")]);(XList [(XSym "and");(XList [(XSym "cons?");(XList [(XSym "tl");(XSym "Select7187")])]);(XList [(XSym "element?");(XSym "Select7195");(XList [(XSym "cons");(XSym "@p");(XList [(XSym "cons");(XSym "@v");(XList [(XSym "cons");(XSym "append");(XList [(XSym "cons");(XSym "and");(XList [(XSym "cons");(XSym "or");(XList [(XSym "cons");(XSym "+");(XList [(XSym "cons");(XSym "*");(XList [(XSym "cons");(XSym "do");(XList [])])])])])])])])])])])])])]);(XList [(XSym "cons");(XSym "Select7195");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "shen.process-assoc");(XList [(XSym "cons");(XSym "Select7195");(XList [(XSym "tl");(XSym "Select7196")])])]);(XList [])])])]);(XList [(XSym "thaw");(XSym "GoTo7181")])])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "shen.@ch");(XSym "Select7195")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7193");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7194");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7193")]);(XList [(XSym "let");(XSym "Select7190");(XList [(XSym "tl");(XSym "Select7193")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7190")]);(XList [(XSym "let");(XSym "Select7192");(XList [(XSym "tl");(XSym "Select7190")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7192")]);(XList [(XSym "and");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7192")])]);(XList [(XSym "and");(XList [(XSym "=");(XList []);(XSym "Select7194")]);(XList [(XSym "=");(XList [(XSym "hd");(XSym "Select7190")]);(XList [(XSym "intern");(XStr [58%N])])])])])])])])])]);(XList [(XSym "let");(XSym "Select7191");(XList [(XSym "tl");(XSym "Select7193")]);(XList [(XSym "shen.cons-form-respect-modes");(XList [(XSym "cons");(XSym "-");(XList [(XSym "cons");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7193")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7191")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "+");(XList [(XSym "tl");(XSym "Select7191")])]);(XList [])])])]);(XList [])])])])]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XSym "Select7194")]);(XList [(XSym "shen.cons-form-respect-modes");(XSym "Select7193")]);(XList [(XSym "thaw");(XSym "GoTo7188")])])])])]);(XList [(XSym "thaw");(XSym "GoTo7188")])]);(XList [(XSym "thaw");(XSym "GoTo7188")])])])])])])])])])])])])])])])])])])])])])])])])])])])])])])]);(XList [(XSym "thaw");(XSym "GoTo7181")])])])]);
 (XList [(XSym "defun");(XSym "shen.process-let");(XList [(XSym "V7213")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "cons?");(XSym "V7213")]);(XList [(XSym "let");(XSym "Select7214");(XList [(XSym "tl");(XSym "V7213")]);(XList [(XSym "and");(XList [(XSym "=");(XSym "let");(XList [(XSym "hd");(XSym "V7213")])]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7214")]);(XList [(XSym "let");(XSym "Select7216");(XList [(XSym "tl");(XSym "Select7214")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7216")]);(XList [(XSym "let");(XSym "Select7217");(XList [(XSym "tl");(XSym "Select7216")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7217")]);(XList [(XSym "cons?");(XList [(XSym "tl");(XSym "Select7217")])])])])])])])])])]);(XList [(XSym "let");(XSym "Select7215");(XList [(XSym "tl");(XSym "V7213")]);(XList [(XSym "cons");(XSym "let");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7215")]);(XList [(XSym "cons");(XList [(XSym "hd");(XList [(XSym "tl");(XSym "Select7215")])]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "let");(XList [(XSym "tl");(XList [(XSym "tl");(XSym "Select7215")])])]);(XList [])])])])])]);(XSym "V7213")])]);
 (XList [(XSym "defun");(XSym "shen.lambda-of-defun");(XList [(XSym "V7237")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "cons?");(XSym "V7237")]);(XList [(XSym "let");(XSym "Select7238");(XList [(XSym "tl");(XSym "V7237")]);(XList [(XSym "and");(XList [(XSym "=");(XSym "defun");(XList [(XSym "hd");(XSym "V7237")])]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7238")]);(XList [(XSym "let");(XSym "Select7240");(XList [(XSym "tl");(XSym "Select7238")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7240")]);(XList [(XSym "let");(XSym "Select7241");(XList [(XSym "hd");(XSym "Select7240")]);(XList [(XSym "let");(XSym "Select7242");(XList [(XSym "tl");(XSym "Select7240")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7241")]);(XList [(XSym "and");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7241")])]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7242")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7242")])])])])])])])])])])])])]);(XList [(XSym "let");(XSym "Select7239");(XList [(XSym "tl");(XSym "V7237")]);(XList [(XSym "eval");(XList [(XSym "cons");(XSym "/.");(XList [(XSym "cons");(XList [(XSym "hd");(XList [(XSym "hd");(XList [(XSym "tl");(XSym "Select7239")])])]);(XList [(XSym "tl");(XList [(XSym "tl");(XSym "Select7239")])])])])])]);(XList [(XSym "shen.f-error");(XSym "shen.lambda-of-defun")])])]);
 (XList [(XSym "defun");(XSym "shen.process-assoc");(XList [(XSym "V7275")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "cons?");(XSym "V7275")]);(XList [(XSym "let");(XSym "Select7276");(XList [(XSym "tl");(XSym "V7275")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7276")]);(XList [(XSym "let");(XSym "Select7279");(XList [(XSym "tl");(XSym "Select7276")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7279")]);(XList [(XSym "cons?");(XList [(XSym "tl");(XSym "Select7279")])])])])])])]);(XList [(XSym "let");(XSym "Select7277");(XList [(XSym "hd");(XSym "V7275")]);(XList [(XSym "let");(XSym "Select7278");(XList [(XSym "tl");(XSym "V7275")]);(XList [(XSym "cons");(XSym "Select7277");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7278")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "Select7277");(XList [(XSym "tl");(XSym "Select7278")])]);(XList [])])])])])]);(XSym "V7275")])])].
Definition share_rewrite_shares : list sx := [(XList [(XSym "defun");(XSym "shen.macros");(XList [(XSym "V7180")]);(XList [(XSym "let");(XSym "GoTo7181");(XList [(XSym "freeze");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "V7180")]);(XList [(XSym "let");(XSym "Select7195");(XList [(XSym "hd");(XSym "V7180")]);(XList [(XSym "let");(XSym "Select7196");(XList [(XSym "tl");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "defmacro");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.process-def");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "defcc");(XSym "Select7195")]);(XList [(XSym "shen.yacc->shen");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "u!");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "cons");(XSym "protect");(XList [(XSym "cons");(XList [(XSym "shen.make-uppercase");(XList [(XSym "hd");(XSym "Select7196")])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "error");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "simple-error");(XList [(XSym "cons");(XList [(XSym "shen.mkstr");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "output");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "pr");(XList [(XSym "cons");(XList [(XSym "shen.mkstr");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stoutput");(XList [])]);(XList [])])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "pr");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "cons");(XSym "pr");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stoutput");(XList [])]);(XList [])])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "make-string");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.mkstr");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "lineread");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "lineread");(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stinput");(XList [])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "input");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "input");(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stinput");(XList [])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "read");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "read");(XList [(XSym "cons");(XList [(XSym "cons");(XSym "stinput");(XList [])]);(XList [])])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "input+");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.process-input+");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "read-byte");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "shen.process-read-byte")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "prolog?");(XSym "Select7195")]);(XList [(XSym "shen.call-prolog");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "defprolog");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.compile-prolog");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "datatype");(XSym "Select7195")]);(XList [(XSym "cons?");(XSym "Select7196")])]);(XList [(XSym "shen.process-datatype");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "tl");(XSym "Select7196")])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "@s");(XSym "Select7195")]);(XList [(XSym "shen.process-@s");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "synonyms");(XSym "Select7195")]);(XList [(XSym "shen.process-synonyms");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "nl");(XSym "Select7195")]);(XList [(XSym "=");(XList []);(XSym "Select7196")])]);(XList [(XSym "cons");(XSym "nl");(XList [(XSym "cons");(XInt (1));(XList [])])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "let");(XSym "Select7195")]);(XList [(XSym "shen.process-let");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "/.");(XSym "Select7195")]);(XList [(XSym "shen.process-lambda");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "cases");(XSym "Select7195")]);(XList [(XSym "shen.process-cases");(XSym "V7180")]);(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "time");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "shen.process-time");(XList [(XSym "hd");(XSym "Select7196")])]);(XList [(XSym "let");(XSym "stage0.lower.else1");(XList [(XSym "freeze");(XList [(XSym "let");(XSym "stage0.lower.else2");(XList [(XSym "freeze");(XList [(XSym "let");(XSym "stage0.lower.else3");(XList [(XSym "freeze");(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "=");(XSym "shen.@c");(XSym "Select7195")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7196")])])])]);(XList [(XSym "shen.rcons_form");(XList [(XSym "hd");(XSym "Select7196")])]);(XList [(XSym "let");(XSym "GoTo7188");(XList [(XSym "freeze");(XList [(XSym "if");(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7187");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "and");(XList [(XSym "cons?");(XSym "Select7187")]);(XList [(XSym "and");(XList [(XSym "cons?");(XList [(XSym "tl");(XSym "Select7187")])]);(XList [(XSym "element?");(XSym "Select7195");(XList [(XSym "cons");(XSym "@p");(XList [(XSym "cons");(XSym "@v");(XList [(XSym "cons");(XSym "append");(XList [(XSym "cons");(XSym "and");(XList [(XSym "cons");(XSym "or");(XList [(XSym "cons");(XSym "+");(XList [(XSym "cons");(XSym "*");(XList [(XSym "cons");(XSym "do");(XList [])])])])])])])])])])])])])]);(XList [(XSym "cons");(XSym "Select7195");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "shen.process-assoc");(XList [(XSym "cons");(XSym "Select7195");(XList [(XSym "tl");(XSym "Select7196")])])]);(XList [])])])]);(XList [(XSym "thaw");(XSym "GoTo7181")])])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "shen.@ch");(XSym "Select7195")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7193");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7194");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "let");(XSym "stage0.lower.else4");(XList [(XSym "freeze");(XList [(XSym "if");(XList [(XSym "=");(XList []);(XSym "Select7194")]);(XList [(XSym "shen.cons-form-respect-modes");(XSym "Select7193")]);(XList [(XSym "thaw");(XSym "GoTo7188")])])]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7193")]);(XList [(XSym "let");(XSym "Select7190");(XList [(XSym "tl");(XSym "Select7193")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7190")]);(XList [(XSym "let");(XSym "Select7192");(XList [(XSym "tl");(XSym "Select7190")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7192")]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7192")])]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XSym "Select7194")]);(XList [(XSym "if");(XList [(XSym "=");(XList [(XSym "hd");(XSym "Select7190")]);(XList [(XSym "intern");(XStr [58%N])])]);(XList [(XSym "let");(XSym "Select7191");(XSym "Select7190");(XList [(XSym "shen.cons-form-respect-modes");(XList [(XSym "cons");(XSym "-");(XList [(XSym "cons");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7193")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7191")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "+");(XSym "Select7192")]);(XList [])])])]);(XList [])])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else4")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else4")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else4")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else4")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else4")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else4")])])])])]);(XList [(XSym "thaw");(XSym "GoTo7188")])]);(XList [(XSym "thaw");(XSym "GoTo7188")])])])])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "unput");(XSym "Select7195")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7186");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7186")]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7186")])]);(XList [(XSym "cons");(XSym "unput");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7186")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "value");(XList [(XSym "cons");(XSym "*property-vector*");(XList [])])]);(XList [])])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else3")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else3")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else3")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else3")])])])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "get");(XSym "Select7195")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7185");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7185")]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7185")])]);(XList [(XSym "cons");(XSym "get");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7185")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "value");(XList [(XSym "cons");(XSym "*property-vector*");(XList [])])]);(XList [])])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else2")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else2")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else2")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else2")])])])]);(XList [(XSym "if");(XList [(XSym "=");(XSym "put");(XSym "Select7195")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7196")]);(XList [(XSym "let");(XSym "Select7182");(XList [(XSym "tl");(XSym "Select7196")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7182")]);(XList [(XSym "let");(XSym "Select7184");(XList [(XSym "tl");(XSym "Select7182")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7184")]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7184")])]);(XList [(XSym "let");(XSym "Select7183");(XSym "Select7182");(XList [(XSym "cons");(XSym "put");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7196")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7183")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7184")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "value");(XList [(XSym "cons");(XSym "*property-vector*");(XList [])])]);(XList [])])])])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])])])])])])])])])])])])])])])])])])])])])])])])])]);(XList [(XSym "thaw");(XSym "GoTo7181")])])])]);
 (XList [(XSym "defun");(XSym "shen.process-let");(XList [(XSym "V7213")]);(XList [(XSym "let");(XSym "stage0.lower.else1");(XList [(XSym "freeze");(XSym "V7213")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "V7213")]);(XList [(XSym "let");(XSym "Select7214");(XList [(XSym "tl");(XSym "V7213")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "let");(XList [(XSym "hd");(XSym "V7213")])]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7214")]);(XList [(XSym "let");(XSym "Select7216");(XList [(XSym "tl");(XSym "Select7214")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7216")]);(XList [(XSym "let");(XSym "Select7217");(XList [(XSym "tl");(XSym "Select7216")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7217")]);(XList [(XSym "if");(XList [(XSym "cons?");(XList [(XSym "tl");(XSym "Select7217")])]);(XList [(XSym "let");(XSym "Select7215");(XSym "Select7214");(XList [(XSym "cons");(XSym "let");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7215")]);(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7216")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "let");(XSym "Select7217")]);(XList [])])])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])])]);
 (XList [(XSym "defun");(XSym "shen.lambda-of-defun");(XList [(XSym "V7237")]);(XList [(XSym "let");(XSym "stage0.lower.else1");(XList [(XSym "freeze");(XList [(XSym "shen.f-error");(XSym "shen.lambda-of-defun")])]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "V7237")]);(XList [(XSym "let");(XSym "Select7238");(XList [(XSym "tl");(XSym "V7237")]);(XList [(XSym "if");(XList [(XSym "=");(XSym "defun");(XList [(XSym "hd");(XSym "V7237")])]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7238")]);(XList [(XSym "let");(XSym "Select7240");(XList [(XSym "tl");(XSym "Select7238")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7240")]);(XList [(XSym "let");(XSym "Select7241");(XList [(XSym "hd");(XSym "Select7240")]);(XList [(XSym "let");(XSym "Select7242");(XList [(XSym "tl");(XSym "Select7240")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7241")]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7241")])]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7242")]);(XList [(XSym "if");(XList [(XSym "=");(XList []);(XList [(XSym "tl");(XSym "Select7242")])]);(XList [(XSym "let");(XSym "Select7239");(XSym "Select7238");(XList [(XSym "eval");(XList [(XSym "cons");(XSym "/.");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7241")]);(XSym "Select7242")])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])])]);
 (XList [(XSym "defun");(XSym "shen.process-assoc");(XList [(XSym "V7275")]);(XList [(XSym "let");(XSym "stage0.lower.else1");(XList [(XSym "freeze");(XSym "V7275")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "V7275")]);(XList [(XSym "let");(XSym "Select7276");(XList [(XSym "tl");(XSym "V7275")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7276")]);(XList [(XSym "let");(XSym "Select7279");(XList [(XSym "tl");(XSym "Select7276")]);(XList [(XSym "if");(XList [(XSym "cons?");(XSym "Select7279")]);(XList [(XSym "if");(XList [(XSym "cons?");(XList [(XSym "tl");(XSym "Select7279")])]);(XList [(XSym "let");(XSym "Select7277");(XList [(XSym "hd");(XSym "V7275")]);(XList [(XSym "let");(XSym "Select7278");(XSym "Select7276");(XList [(XSym "cons");(XSym "Select7277");(XList [(XSym "cons");(XList [(XSym "hd");(XSym "Select7278")]);(XList [(XSym "cons");(XList [(XSym "cons");(XSym "Select7277");(XSym "Select7279")]);(XList [])])])])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])]);(XList [(XSym "thaw");(XSym "stage0.lower.else1")])])])])].
Theorem share_rewrites_validated : judge_share_all share_rewrite_forms share_rewrite_shares =
 [SAccepted (of_string "shen.macros"); SAccepted (of_string "shen.process-let");
  SAccepted (of_string "shen.lambda-of-defun"); SAccepted (of_string "shen.process-assoc")].
Proof. vm_compute. reflexivity. Qed.
Local Close Scope string_scope.

(* ---------- soundness ---------- *)
Definition andRs (m : nat) : list frame := repeat KAndR m.

(* ---------- FrontHyps from the proved compatibility lemmas (r1-share-ht) ----------
   Every field of JitFrontCheck.FrontHyps is now a closed theorem except D_wf, which is a property
   of D: KRef_refl and compat_trap, compat_app, compat_call from JitKRefFund (KRef's fundamental
   property, option A), the control compatibility lemmas from JitKRefCompatCtl, lambda and freeze
   from JitKRefCompatClo, scope and anti-reduction from JitKRefBase (JitFrontCheck's
   front_scope_proved and front_anti_proved). So FrontHyps is D_wf, and check_share_sound below
   takes D_wf, not FrontHyps. *)
Section Hyps.
Variables (sealed : list name) (D : list (name * fundef)).
Theorem front_hyps : JitKRef.JitKRef.D_wf sealed D -> FrontHyps sealed D.
Proof.
 intros Dw. constructor.
 - exact Dw.
 - exact (JitKRefFund.JitKRefFund.KRef_refl sealed D).
 - exact (front_scope_proved sealed D).
 - exact (front_anti_proved sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_var sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_let sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_if sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_and sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_or sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_cond sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_type sealed D).
 - exact (JitKRefFund.JitKRefFund.compat_trap sealed D).
 - exact (JitKRefCompatClo.JitKRefCompatClo.compat_lambda sealed D).
 - exact (JitKRefCompatClo.JitKRefCompatClo.compat_freeze sealed D).
 - exact (JitKRefFund.JitKRefFund.compat_call sealed D).
 - exact (JitKRefFund.JitKRefFund.compat_app sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_defun sealed D).
Qed.
End Hyps.

Section Share.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (JitKRef.JitKRef.srun sealed).
Notation ObsT := (JitKRef.JitKRef.ObsT sealed).
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation SRel := (JitKRef.JitKRef.SRel sealed D).
Notation KRel := (JitKRef.JitKRef.KRel sealed D).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation rule_sound := (JitFrontCheck.rule_sound sealed D).
Notation chk_sound := (JitFrontCheck.chk_sound sealed D).

(* D defines thaw as the kernel does: (defun thaw (V) (V)). *)
Variable tp : name.
Hypothesis HT : In (thaw_name, FUser [tp] (EApp (EVar tp) [])) D.

Lemma SRel_with_cell_tgt : forall k w s0 s, SRel k w s0 s -> SRel k w s0 (with_cell s).
Proof.
 intros k w s0 s (W & H0 & H1 & G & Gv & Hp).
 split; [exact W|split; [exact H0|split; [exact H1|split; [exact G|split; [exact Gv|]]]]].
 intros l0 l I. destruct (Hp _ _ I) as (c0 & c & N0 & N & F). exists c0, c. split; [exact N0|split; [|exact F]].
 cbn. rewrite nth_error_app1; [exact N|]. apply nth_error_Some. congruence.
Qed.

Lemma srun_throw_frames : forall Fs x K s, forallb KB.nontrap Fs = true ->
 srun (Cfg (Throw x) (Fs ++ K) s) [] (Cfg (Throw x) K s).
Proof.
 induction Fs as [|f Fs IH]; intros x K s N; cbn in *; [apply KB.srun_refl|].
 apply andb_true_iff in N as [N1 N2].
 eapply KB.srun_tau; [apply KB.throw_frame_next; exact N1|apply IH; exact N2].
Qed.

Lemma obs_throw_tgt : forall k w x K0 K s0 s f, KB.nontrap f = true ->
 ObsT k w (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s) -> ObsT (S k) w (Cfg (Throw x) K0 s0) (Cfg (Throw x) (f :: K) s).
Proof.
 intros k w x K0 K s0 s f N H. apply KB.ObsT_step.
 - unfold KB.nonterm. rewrite KB.throw_frame_next by exact N. exact I.
 - intros l c1 St. destruct (KB.step_r_cases sealed _ _ _ St) as [[E ->]|[(q & kk & r & E & _)|(r & y & Rc & _)]].
   + rewrite KB.throw_frame_next in E by exact N. injection E as <-. apply KB.ObsT_ObsTr. exact H.
   + rewrite KB.throw_frame_next in E by exact N. discriminate.
   + cbn in Rc. discriminate.
Qed.

(* A throw through non-trap frames on both sides: the source pops silently, the target pays one
   index per frame. *)
Lemma throw_pop : forall k w K0 K Fs0 Fs, KRel k w K0 K -> forallb KB.nontrap Fs0 = true ->
 forallb KB.nontrap Fs = true ->
 forall j w' x s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s ->
 ObsT j w' (Cfg (Throw x) (Fs0 ++ K0) s0) (Cfg (Throw x) (Fs ++ K) s).
Proof.
 intros k w K0 K Fs0 Fs HK N0 N j w' x s0 s L W HS.
 eapply KB.ObsT_anti; [apply srun_throw_frames; exact N0|].
 revert j L HS N. induction Fs as [|f Fs IH]; intros j L HS N; cbn [app].
 - apply (KB.KRel_throw sealed D); [eapply KB.KRel_mono; eauto|exact HS].
 - cbn in N. apply andb_true_iff in N as [N1 N2]. destruct j as [|j]; [apply KB.ObsT_0|].
   apply obs_throw_tgt; [exact N1|]. apply IH; [lia|eapply KB.SRel_down; [|exact HS]; lia|exact N2].
Qed.

(* A target frame f against a list of source frames: the Throw clause is throw_pop's, the Ret
   clause is given. *)
Lemma krel_build : forall k w K0 K Fs0 f, KRel k w K0 K -> forallb KB.nontrap Fs0 = true -> KB.nontrap f = true ->
 (forall j w' v0 v s0 s c1, (S j <= k)%nat -> wext w w' -> VRel (S j) w' v0 v -> SRel (S j) w' s0 s ->
   next_r R P (Cfg (Ret v) (f :: K) s) = MTau c1 ->
   exists c0', srun (Cfg (Ret v0) (Fs0 ++ K0) s0) [] c0' /\ ObsT j w' c0' c1) ->
 (forall v s, exists c1, next_r R P (Cfg (Ret v) (f :: K) s) = MTau c1) ->
 KRel k w (Fs0 ++ K0) (f :: K).
Proof.
 intros k w K0 K Fs0 f HK N0 N Ht Hm. apply KB.KRel_iff. intros j L w' W. split.
 - intros v0 v s0 s HV HS. destruct j as [|j]; [apply KB.ObsT_0|].
   destruct (Hm v s) as [c1 E]. apply KB.ObsT_running.
   + reflexivity.
   + unfold KB.nonterm. rewrite E. exact I.
   + intros x. cbn [kont mem]. apply (throw_pop k w K0 K Fs0 [f]); [exact HK|exact N0|cbn; rewrite N; reflexivity|lia|exact W|].
     eapply KB.SRel_down; [|exact HS]; lia.
   + intros c2 E2. apply (Ht j w' v0 v s0 s c2); [lia|exact W|exact HV|exact HS|exact E2].
   + intros q kk r E2. rewrite E in E2. discriminate.
 - intros x s0 s HS. apply (throw_pop k w K0 K Fs0 [f]); [exact HK|exact N0|cbn; rewrite N; reflexivity|exact L|exact W|exact HS].
Qed.

(* One target step from a running source that stays put. *)
Lemma tgt_tau : forall k w c0 c c1, running_state c0 = true -> next_r R P c = MTau c1 ->
 (forall x, ObsT k w (Cfg (Throw x) (kont c0) (mem c0)) (Cfg (Throw x) (kont c) (mem c))) ->
 ObsT k w c0 c1 -> ObsT (S k) w c0 c.
Proof.
 intros k w c0 c c1 R0 E Hx H. apply KB.ObsT_running; [exact R0|unfold KB.nonterm; rewrite E; exact I|exact Hx| |].
 - intros c2 E2. rewrite E in E2. injection E2 as <-. exists c0. split; [apply KB.srun_refl|exact H].
 - intros q kk r E2. rewrite E in E2. discriminate.
Qed.

Lemma nontrap_andRs : forall m f, KB.nontrap f = true -> forallb KB.nontrap (andRs m ++ [f]) = true.
Proof. induction m; intros f N; cbn; [rewrite N; reflexivity|apply IHm; exact N]. Qed.

Lemma stack_eq : forall m f K0, andRs m ++ f :: K0 = (andRs m ++ [f]) ++ K0.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma srun_andRs : forall m b K s, srun (Cfg (Ret (VBool b)) (andRs m ++ K) s) [] (Cfg (Ret (VBool b)) K s).
Proof.
 induction m; intros b K s; cbn; [apply KB.srun_refl|].
 eapply KB.srun_tau; [reflexivity|apply IHm].
Qed.

(* Where the source goes when a value reaches its KAndR frames and the chain's if. *)
Lemma src_ret : forall m X Y rho0 K0 v s0,
 match KB.asbool v with
 | Some true => srun (Cfg (Ret v) (andRs m ++ KIf X Y rho0 :: K0) s0) [] (Cfg (Eval rho0 X) K0 s0)
 | Some false => srun (Cfg (Ret v) (andRs m ++ KIf X Y rho0 :: K0) s0) [] (Cfg (Eval rho0 Y) K0 s0)
 | None => srun (Cfg (Ret v) (andRs m ++ KIf X Y rho0 :: K0) s0) [] (Cfg (Throw XNotBoolean) K0 s0)
 end.
Proof.
 intros m X Y rho0 K0 v s0. destruct (KB.asbool v) as [b|] eqn:Ab.
 - assert (Ev : v = VBool b) by (destruct v; cbn in Ab; congruence). subst v.
   destruct b; cbv beta iota; change (@nil event) with (@nil event ++ @nil event);
    (eapply KB.srun_trans; [apply srun_andRs|]).
   + apply (KB.srun_tau sealed _ (Cfg (Eval rho0 X) K0 s0)); [reflexivity|apply KB.srun_refl].
   + apply (KB.srun_tau sealed _ (Cfg (Eval rho0 Y) K0 s0)); [reflexivity|apply KB.srun_refl].
 - destruct m as [|m].
   + apply (KB.srun_tau sealed _ (Cfg (Throw XNotBoolean) K0 s0)); [|apply KB.srun_refl].
     cbn [andRs repeat app]. rewrite KB.next_KIf, Ab. reflexivity.
   + change (andRs (S m) ++ KIf X Y rho0 :: K0) with (KAndR :: (andRs m ++ KIf X Y rho0 :: K0)).
     apply (KB.srun_tau sealed _ (Cfg (Throw XNotBoolean) (andRs m ++ KIf X Y rho0 :: K0) s0)).
     * rewrite KB.next_KAndR, Ab. reflexivity.
     * rewrite stack_eq. apply srun_throw_frames. apply nontrap_andRs. reflexivity.
Qed.

(* (thaw G), G bound to the frozen Y': six target steps to Y' in the closure's environment. *)
Theorem thaw_erel : forall k w rho0 Y rhoi G Y' rT,
 lookup G rhoi = Some (VFrozen Y' rT) -> ERel k w rho0 Y rT Y' -> ERel k w rho0 Y rhoi (thaw_e G).
Proof.
 intros k w rho0 Y rhoi G Y' rT LG He. apply KB.ERel_iff. intros j L w' W K0 K HK s0 s HS.
 assert (Ht : lookup thaw_name (gfuns s) = Some (FUser [tp] (EApp (EVar tp) []))).
 { destruct HS as (_ & _ & H1 & _). apply H1. exact HT. }
 set (fr := VFrozen Y' rT).
 assert (Thr : forall Fs j', forallb KB.nontrap Fs = true -> (j' <= j)%nat ->
   forall x, ObsT j' w' (Cfg (Throw x) K0 s0) (Cfg (Throw x) (Fs ++ K) s)).
 { intros Fs j' N L' x. apply (throw_pop j w' K0 K [] Fs HK eq_refl N j' w' x s0 s L');
    [eapply KB.wext_self; exact HS|eapply KB.SRel_down; [|exact HS]; lia]. }
 destruct j as [|j1]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval rhoi (EVar G)) (KCallArgs thaw_name [] [] rhoi :: K) s)); [reflexivity|reflexivity| |].
 { intros x. apply (Thr []); [reflexivity|lia]. }
 destruct j1 as [|j2]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Ret fr) (KCallArgs thaw_name [] [] rhoi :: K) s)); [reflexivity|apply KB.sval_next; exact LG| |].
 { intros x. apply (Thr [KCallArgs thaw_name [] [] rhoi]); [reflexivity|lia]. }
 destruct j2 as [|j3]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval [(tp, fr)] (EApp (EVar tp) [])) K s)); [reflexivity| | |].
 { change (call_named_r R P thaw_name [fr] K s = MTau (Cfg (Eval (combine [tp] [fr]) (EApp (EVar tp) [])) K s)).
   apply (KB.call_named_user sealed thaw_name [tp] (EApp (EVar tp) []) [fr] K s Ht). reflexivity. }
 { intros x. apply (Thr [KCallArgs thaw_name [] [] rhoi]); [reflexivity|lia]. }
 destruct j3 as [|j4]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval [(tp, fr)] (EVar tp)) (KHead [] [(tp, fr)] :: K) s)); [reflexivity|reflexivity| |].
 { intros x. apply (Thr []); [reflexivity|lia]. }
 destruct j4 as [|j5]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Ret fr) (KHead [] [(tp, fr)] :: K) s)); [reflexivity|apply KB.sval_next; change (lookup tp [(tp, fr)] = Some fr); cbn [lookup]; rewrite text_eqb_refl; reflexivity| |].
 { intros x. apply (Thr [KHead [] [(tp, fr)]]); [reflexivity|lia]. }
 destruct j5 as [|j6]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval rT Y') K s)); [reflexivity|reflexivity| |].
 { intros x. apply (Thr [KHead [] [(tp, fr)]]); [reflexivity|lia]. }
 eapply KB.ERel_apply; [exact He|lia|exact W| |eapply KB.SRel_down; [|exact HS]; lia].
 eapply KB.KRel_down; [|exact HK]. lia.
Qed.

(* The base of a chain: the source's KAndR frames and if, against the target's (if T' X' (thaw G)). *)
Lemma kif_base : forall k w m X Y rho0 X' G rhoi K0 K,
 KRel k w K0 K ->
 (forall j w', (j <= k)%nat -> wext w w' -> ERel j w' rho0 X rhoi X') ->
 (forall j w', (j <= k)%nat -> wext w w' -> ERel j w' rho0 Y rhoi (thaw_e G)) ->
 KRel k w (andRs m ++ KIf X Y rho0 :: K0) (KIf X' (thaw_e G) rhoi :: K).
Proof.
 intros k w m X Y rho0 X' G rhoi K0 K HK HX HY. rewrite stack_eq.
 apply krel_build; [exact HK|apply nontrap_andRs; reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite KB.next_KIf in E. injection E as <-.
   rewrite <- stack_eq. pose proof (src_ret m X Y rho0 K0 v0 s0) as Sr.
   rewrite (KB.VRel_asbool sealed D _ _ _ _ HV) in Sr.
   destruct (KB.asbool v) as [[|]|]; eexists; (split; [exact Sr|]).
   + eapply KB.ERel_apply; [apply (HX (S j) w'); [lia|exact W]|apply le_S, le_n|eapply KB.wext_self; exact HS| |].
     * eapply KB.KRel_mono; [|exact W|exact HK]. lia.
     * eapply KB.SRel_down; [|exact HS]; lia.
   + eapply KB.ERel_apply; [apply (HY (S j) w'); [lia|exact W]|apply le_S, le_n|eapply KB.wext_self; exact HS| |].
     * eapply KB.KRel_mono; [|exact W|exact HK]. lia.
     * eapply KB.SRel_down; [|exact HS]; lia.
   + apply (KB.KRel_throw sealed D).
     * eapply KB.KRel_mono; [|exact W|exact HK]. lia.
     * eapply KB.SRel_down; [|exact HS]; lia.
 - intros v s. rewrite KB.next_KIf. eexists. reflexivity.
Qed.

(* A chain's `and`: the source's KAnd over its KAndR frames and if, against the target's
   (if T' U (thaw G)), given the rest of the chain (IH). *)
Lemma kand_frame : forall k w m X Y rho0 G rhoi rho0i Sc U K0 K,
 KRel k w K0 K ->
 (forall j w', (j <= k)%nat -> wext w w' -> ERel j w' rho0 Y rhoi (thaw_e G)) ->
 (forall j w' s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s ->
    ObsT j w' (Cfg (Eval rho0i Sc) (andRs (S m) ++ KIf X Y rho0 :: K0) s0) (Cfg (Eval rhoi U) K s)) ->
 KRel k w (KAnd Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) (KIf U (thaw_e G) rhoi :: K).
Proof.
 intros k w m X Y rho0 G rhoi rho0i Sc U K0 K HK HY IH.
 change (KAnd Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) with ([KAnd Sc rho0i] ++ andRs m ++ KIf X Y rho0 :: K0).
 rewrite stack_eq, app_assoc.
 apply krel_build; [exact HK|cbn; apply nontrap_andRs; reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite KB.next_KIf in E. injection E as <-.
   rewrite <- app_assoc, <- stack_eq. cbn [app].
   pose proof (KB.next_KAnd sealed v0 Sc rho0i (andRs m ++ KIf X Y rho0 :: K0) s0) as E0.
   rewrite (KB.VRel_asbool sealed D _ _ _ _ HV) in E0.
   destruct (KB.asbool v) as [[|]|] eqn:Ab.
   + eexists; split; [eapply KB.srun_tau; [exact E0|apply KB.srun_refl]|].
     apply IH; [lia|exact W|eapply KB.SRel_down; [|exact HS]; lia].
   + eexists; split.
     * eapply KB.srun_tau; [exact E0|]. exact (src_ret m X Y rho0 K0 (VBool false) s0).
     * eapply KB.ERel_apply; [apply (HY (S j) w'); [lia|exact W]|apply le_S, le_n|eapply KB.wext_self; exact HS| |].
       -- eapply KB.KRel_mono; [|exact W|exact HK]. lia.
       -- eapply KB.SRel_down; [|exact HS]; lia.
   + eexists; split.
     * eapply KB.srun_tau; [exact E0|]. rewrite stack_eq. apply srun_throw_frames. apply nontrap_andRs. reflexivity.
     * apply (KB.KRel_throw sealed D).
       -- eapply KB.KRel_mono; [|exact W|exact HK]. lia.
       -- eapply KB.SRel_down; [|exact HS]; lia.
 - intros v s. rewrite KB.next_KIf. eexists. reflexivity.
Qed.

Lemma bound_false : forall g x, bound g x = false -> ~ In x g.
Proof.
 intros g x B I. unfold bound in B. assert (existsb (text_eqb x) g = true); [|congruence].
 apply existsb_exists. exists x. split; [exact I|apply text_eqb_refl].
Qed.

Lemma EnvRel_cons_r : forall k w g x v r0 r, ~ In x g ->
 EnvRel_with (VRel k) w g r0 r -> EnvRel_with (VRel k) w g r0 ((x, v) :: r).
Proof.
 intros k w g x v r0 r N H y I. destruct (H y I) as (a0 & a & E0 & E1 & V). exists a0, a.
 split; [exact E0|split; [|exact V]]. cbn. destruct (text_eqb y x) eqn:T; [|exact E1].
 apply text_eqb_eq in T. subst. contradiction.
Qed.

Lemma EnvRel_cons_same : forall k w g x v0 v r0 r, VRel k w v0 v ->
 EnvRel_with (VRel k) w g r0 r -> EnvRel_with (VRel k) w (x :: g) ((x, v0) :: r0) ((x, v) :: r).
Proof.
 intros k w g x v0 v r0 r Hv H y I. cbn. destruct (text_eqb y x) eqn:T.
 - exists v0, v. auto.
 - destruct I as [<-|I]; [rewrite text_eqb_refl in T; discriminate|]. exact (H y I).
Qed.

(* The chain, in the form the induction needs: from any related continuations and stores, the
   source evaluating C over m KAndR frames and the chain's if is related to the target evaluating
   U. *)
(* ---------- share's reuse: soundness ----------
   HP: D holds hd and tl as the primitives, so that a path re-evaluated on the source gives the
   value the target's variable was bound to. Dw: D_wf, for the named-call congruence of then_chk
   (JitKRefCompatCall.compat_call_core from fund_below, which JitKRefFund proves from D_wf). *)
Hypothesis HP : In (hd_name, FPrim PHd) D /\ In (tl_name, FPrim PTl) D.
Hypothesis Dw : JitKRef.JitKRef.D_wf sealed D.

Definition hd_tl (s : store) : Prop :=
 lookup hd_name (gfuns s) = Some (FPrim PHd) /\ lookup tl_name (gfuns s) = Some (FPrim PTl).

Lemma hd_tl_src : forall k w s0 s, SRel k w s0 s -> hd_tl s0.
Proof. intros k w s0 s (_ & H0 & _). split; apply H0; [exact (proj1 HP)|exact (proj2 HP)]. Qed.
Lemma hd_tl_tgt : forall k w s0 s, SRel k w s0 s -> hd_tl s.
Proof. intros k w s0 s (_ & _ & H1 & _). split; apply H1; [exact (proj1 HP)|exact (proj2 HP)]. Qed.

Lemma op_of_some : forall f o, op_of f = Some o -> f = (if o then hd_name else tl_name).
Proof.
 intros f o H. unfold op_of in H. destruct (text_eqb f hd_name) eqn:E1.
 - injection H as <-. apply text_eqb_eq. exact E1.
 - destruct (text_eqb f tl_name) eqn:E2; [|discriminate]. injection H as <-. apply text_eqb_eq. exact E2.
Qed.

Lemma prim_pop_next : forall (o : bool) v rho K s, hd_tl s ->
 next_r R P (Cfg (Ret v) (KCallArgs (if o then hd_name else tl_name) [] [] rho :: K) s) =
 MTau (match pop o v with Some a => Cfg (Ret a) K s | None => Cfg (Throw (XPrim (if o then PHd else PTl))) K s end).
Proof.
 intros o v rho K s [Hh Ht].
 change (next_r R P (Cfg (Ret v) (KCallArgs (if o then hd_name else tl_name) [] [] rho :: K) s))
   with (call_named_r R P (if o then hd_name else tl_name) [v] K s).
 unfold call_named_r. destruct o; [rewrite Hh|rewrite Ht]; destruct v; reflexivity.
Qed.

Lemma pops_app : forall ops0 ops v, pops v (ops0 ++ ops) = match pops v ops0 with Some v' => pops v' ops | None => None end.
Proof. induction ops0 as [|o ops0 IH]; intros ops v; cbn; [reflexivity|]. destruct (pop o v); [apply IH|reflexivity]. Qed.

(* Related values have the same shape under hd and tl. *)
Lemma VRel_pop : forall o k w v0 v, VRel k w v0 v ->
 match pop o v0, pop o v with Some a0, Some a => VRel k w a0 a | None, None => True | _, _ => False end.
Proof.
 intros o k w v0 v H. rewrite (JitKRefGround.JitKRefGround.VRel_unfold sealed D k) in H.
 destruct v0, v; cbn in H |- *; try contradiction; try exact I.
 destruct H as [H1 H2]. rewrite (JitKRefGround.JitKRefGround.VRel_unfold sealed D k). destruct o; assumption.
Qed.

Lemma VRel_pops : forall ops k w v0 v a, VRel k w v0 v -> pops v ops = Some a -> exists a0, pops v0 ops = Some a0 /\ VRel k w a0 a.
Proof.
 induction ops as [|o ops IH]; intros k w v0 v a H E; cbn in E |- *.
 - injection E as <-. exists v0. split; [reflexivity|exact H].
 - pose proof (VRel_pop o k w v0 v H) as Hp. destruct (pop o v) as [v'|]; [|discriminate].
   destruct (pop o v0) as [a0|]; [|contradiction]. exact (IH _ _ _ _ _ Hp E).
Qed.

Lemma src_path : forall e x ops rho vx v K s, path_of e = Some (x, ops) -> lookup x rho = Some vx ->
 pops vx ops = Some v -> hd_tl s -> srun (Cfg (Eval rho e) K s) [] (Cfg (Ret v) K s).
Proof.
 induction e using expr_ind'; intros x0 ops rho vx v K st Hp Hx Hv Hs; cbn in Hp; try discriminate.
 - injection Hp as <- <-. cbn in Hv. injection Hv as <-.
   eapply KB.srun_tau; [apply KB.sval_next; cbn; exact Hx|apply KB.srun_refl].
 - destruct l as [|a [|b l]]; try discriminate.
   destruct (op_of f) as [o|] eqn:Eo; [|discriminate]. destruct (path_of a) as [[y ops']|] eqn:Ea; [|discriminate].
   injection Hp as <- <-. rewrite (op_of_some f o Eo).
   rewrite pops_app in Hv. destruct (pops vx ops') as [va|] eqn:Ev; [|discriminate]. cbn in Hv.
   destruct (pop o va) as [v'|] eqn:Eop; [|discriminate]. injection Hv as <-.
   inversion H as [|a' l' Ha _]; subst.
   apply (KB.srun_tau sealed _ (Cfg (Eval rho a) (KCallArgs (if o then hd_name else tl_name) [] [] rho :: K) st)); [reflexivity|].
   change (@nil event) with (@nil event ++ @nil event). eapply KB.srun_trans; [eapply Ha; eauto|].
   eapply KB.srun_tau; [rewrite (prim_pop_next o va rho K st Hs), Eop; reflexivity|apply KB.srun_refl].
Qed.

(* Facts: every entry holds (not only the first per name), so a let that rebinds x keeps the
   others valid once fdrop has removed those about x or over x. *)
Definition FactsAll (Pf : facts) (rho : lenv) : Prop := forall y p, In (y, p) Pf ->
 exists v vb, lookup y rho = Some v /\ lookup (fst p) rho = Some vb /\ pops vb (snd p) = Some v.

Lemma flookup_in : forall y Pf p, flookup y Pf = Some p -> In (y, p) Pf.
Proof.
 intros y Pf. induction Pf as [|[z q] Pf IH]; intros p E; cbn in E; [discriminate|].
 destruct (text_eqb y z) eqn:T; [injection E as <-; apply text_eqb_eq in T; subst; left; reflexivity|right; apply IH; exact E].
Qed.

Lemma lookup_other : forall {A} y x (v : A) rho, text_eqb y x = false -> lookup y ((x, v) :: rho) = lookup y rho.
Proof. intros A y x v rho T. cbn. rewrite T. reflexivity. Qed.

Lemma FactsAll_nil : forall rho, FactsAll [] rho.
Proof. intros rho y p []. Qed.

Lemma fdrop_in : forall x Pf y p, In (y, p) (fdrop x Pf) -> In (y, p) Pf /\ text_eqb y x = false /\ text_eqb (fst p) x = false.
Proof.
 intros x Pf y p I. unfold fdrop in I. apply filter_In in I as [I B]. cbn in B.
 apply andb_true_iff in B as [B1 B2]. apply negb_true_iff in B1, B2. auto.
Qed.

Lemma FactsAll_drop : forall Pf rho x v, FactsAll Pf rho -> FactsAll (fdrop x Pf) ((x, v) :: rho).
Proof.
 intros Pf rho x v H y p I. destruct (fdrop_in x Pf y p I) as (I' & T1 & T2).
 rewrite !lookup_other by assumption. exact (H y p I').
Qed.

Lemma FactsAll_add : forall Pf rho x v b ops vb, FactsAll Pf rho -> lookup b rho = Some vb -> pops vb ops = Some v ->
 text_eqb b x = false -> FactsAll ((x, (b, ops)) :: fdrop x Pf) ((x, v) :: rho).
Proof.
 intros Pf rho x v b ops vb H Hb Hv T y p [E|I].
 - injection E as <- <-. exists v, vb. cbn [fst snd]. rewrite (lookup_other b x v rho T). cbn. rewrite text_eqb_refl. auto.
 - exact (FactsAll_drop Pf rho x v H y p I).
Qed.

Lemma FactsAll_incl : forall P1 P2 rho, incl P1 P2 -> FactsAll P2 rho -> FactsAll P1 rho.
Proof. intros P1 P2 rho I H y p J. exact (H y p (I _ J)). Qed.

Lemma path_eqb_eq : forall p q, path_eqb p q = true -> p = q.
Proof.
 intros [x ops] [y qs] E. unfold path_eqb in E. cbn [fst snd] in E. apply andb_true_iff in E as [E1 E2].
 apply text_eqb_eq in E1. subst y. f_equal. revert qs E2. induction ops as [|o ops IH]; intros [|q qs] E; cbn in E; try discriminate; [reflexivity|].
 apply andb_true_iff in E as [E3 E4]. apply Bool.eqb_prop in E3. subst q. rewrite (IH qs E4). reflexivity.
Qed.

Lemma bound_in : forall g x, bound g x = true -> In x g.
Proof.
 intros g x B. unfold bound in B. apply existsb_exists in B as (y & I & T). apply text_eqb_eq in T. subst y. exact I.
Qed.

Lemma canon_val : forall Pf rho e x ops b ops', FactsAll Pf rho -> path_of e = Some (x, ops) -> canon Pf e = Some (b, ops') ->
 forall vb v, lookup b rho = Some vb -> pops vb ops' = Some v -> exists vx, lookup x rho = Some vx /\ pops vx ops = Some v.
Proof.
 intros Pf rho e x ops b ops' HF Hp Hc vb v Hb Hv. unfold canon in Hc. rewrite Hp in Hc.
 destruct (flookup x Pf) as [[b0 ops0]|] eqn:Hl.
 - injection Hc as <- <-. destruct (HF x (b0, ops0) (flookup_in _ _ _ Hl)) as (vx & vb' & E1 & E2 & E3). cbn [fst snd] in E2, E3.
   rewrite Hb in E2. injection E2 as <-. rewrite pops_app, E3 in Hv. exists vx. split; assumption.
 - injection Hc as <- <-. exists vb. split; assumption.
Qed.

Definition ThenInv (k : nat) (w : world) (g : list name) (Ps Pt : facts) (rho0 rho : lenv) : Prop :=
 wf_world w /\ EnvRel_with (VRel k) w g rho0 rho /\ FactsAll Ps rho0 /\ FactsAll Pt rho.

Lemma ThenInv_mono : forall k j w w' g Ps Pt r0 r, (j <= k)%nat -> wext w w' -> ThenInv k w g Ps Pt r0 r -> ThenInv j w' g Ps Pt r0 r.
Proof.
 intros k j w w' g Ps Pt r0 r L W (Wf & HE & H1 & H2). split; [exact (proj2 W)|split; [eapply KB.EnvRel_mono; eauto|split; assumption]].
Qed.

(* What a reused path gives: the source's path and the target's variable hold related values, each
   the reused path's value on its side. *)
Lemma reuse_path_vals : forall k w g Ps Pt rho0 rho X y p, ThenInv k w g Ps Pt rho0 rho ->
 reuse_path g Ps Pt X (EVar y) = Some p ->
 exists x ops vx v0 v vb0 vb, path_of X = Some (x, ops) /\ lookup x rho0 = Some vx /\ pops vx ops = Some v0 /\
   lookup y rho = Some v /\ VRel k w v0 v /\
   lookup (fst p) rho0 = Some vb0 /\ pops vb0 (snd p) = Some v0 /\ lookup (fst p) rho = Some vb /\ pops vb (snd p) = Some v.
Proof.
 intros k w g Ps Pt rho0 rho X y p (Wf & HE & HFs & HFt) Hr. unfold reuse_path in Hr.
 destruct (flookup y Pt) as [p'|] eqn:Hy; [|discriminate]. destruct (canon Ps X) as [q|] eqn:Hc; [|discriminate].
 destruct (path_eqb p' q && bound g (fst p')) eqn:B; [|discriminate]. injection Hr as <-.
 apply andb_true_iff in B as [B1 B2]. apply path_eqb_eq in B1. subst q.
 destruct (HFt y p' (flookup_in _ _ _ Hy)) as (v & vb & Ey & Eb & Ev).
 destruct (HE (fst p') (bound_in _ _ B2)) as (vb0 & vb' & Eb0 & Eb' & HV). rewrite Eb in Eb'. injection Eb' as <-.
 destruct (VRel_pops (snd p') k w vb0 vb v HV Ev) as (v0 & Ev0 & HV0).
 assert (Hp : exists xo, path_of X = Some xo) by (unfold canon in Hc; destruct (path_of X); [eauto|discriminate]).
 destruct Hp as ([x ops] & Hp). destruct p' as [b ops'].
 destruct (canon_val Ps rho0 X x ops b ops' HFs Hp Hc vb0 v0 Eb0 Ev0) as (vx & Ex & Evx).
 exists x, ops, vx, v0, v, vb0, vb. auto 10.
Qed.

(* Throws from the source's continuation against target frames, at every lower index. *)
Lemma thr : forall k w K0 K s0 s, KRel k w K0 K -> SRel k w s0 s -> forall Fs j x, forallb KB.nontrap Fs = true ->
 (j <= k)%nat -> ObsT j w (Cfg (Throw x) K0 s0) (Cfg (Throw x) (Fs ++ K) s).
Proof.
 intros k w K0 K s0 s HK HS Fs j x N L.
 apply (throw_pop k w K0 K [] Fs HK eq_refl N j w x s0 s L); [eapply KB.wext_self; exact HS|eapply KB.SRel_down; [|exact HS]; exact L].
Qed.

Lemma ERel_reuse_var : forall k w g Ps Pt rho0 rho X y p, ThenInv k w g Ps Pt rho0 rho ->
 reuse_path g Ps Pt X (EVar y) = Some p -> ERel k w rho0 X rho (EVar y).
Proof.
 intros k w g Ps Pt rho0 rho X y p Hi Hr.
 destruct (reuse_path_vals k w g Ps Pt rho0 rho X y p Hi Hr) as (x & ops & vx & v0 & v & _ & _ & Hp & Ex & Ev0 & Ey & HV & _).
 apply KB.ERel_iff. intros j L w' W K0 K HK s0 s HS. destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Ret v) K s)); [reflexivity|apply KB.sval_next; cbn; exact Ey| |].
 - intros x'. apply (thr (S j) w' K0 K s0 s HK HS []); [reflexivity|lia].
 - eapply KB.ObsT_anti; [apply (src_path X x ops rho0 vx v0 K0 s0 Hp Ex Ev0); eapply hd_tl_src; exact HS|].
   apply (KB.KRel_ret sealed D); [eapply KB.KRel_down; [|exact HK]; lia|eapply KB.VRel_mono; [|exact W|exact HV]; lia|eapply KB.SRel_down; [|exact HS]; lia].
Qed.

Lemma EnvRel_cons_same' : forall k w g x v0 v r0 r, VRel k w v0 v ->
 EnvRel_with (VRel k) w g r0 r -> EnvRel_with (VRel k) w (x :: g) ((x, v0) :: r0) ((x, v) :: r).
Proof.
 intros k w g x v0 v r0 r Hv H y I. cbn. destruct (text_eqb y x) eqn:T.
 - exists v0, v. auto.
 - destruct I as [<-|I]; [rewrite text_eqb_refl in T; discriminate|]. exact (H y I).
Qed.

(* A then-branch let whose bound expression is a reused path: the source evaluates the path, the
   target reads its variable; the fact is recorded on both sides. *)
Lemma ERel_reuse_let : forall k w g Ps Pt rho0 rho x a b0 y b p, ThenInv k w g Ps Pt rho0 rho ->
 reuse_path g Ps Pt a (EVar y) = Some p -> text_eqb (fst p) x = false ->
 (forall j w' v0 v, (j <= k)%nat -> wext w w' ->
   ThenInv j w' (x :: g) ((x, p) :: fdrop x Ps) ((x, p) :: fdrop x Pt) ((x, v0) :: rho0) ((x, v) :: rho) ->
   ERel j w' ((x, v0) :: rho0) b0 ((x, v) :: rho) b) ->
 ERel k w rho0 (ELet x a b0) rho (ELet x (EVar y) b).
Proof.
 intros k w g Ps Pt rho0 rho x a b0 y b p Hi Hr Tx Hb.
 destruct (reuse_path_vals k w g Ps Pt rho0 rho a y p Hi Hr) as (x1 & ops & vx & v0 & v & vb0 & vb & Hp & Ex & Ev0 & Ey & HV & Eb0 & Ep0 & Eb & Ep).
 apply KB.ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval rho (EVar y)) (KLet x b rho :: K) s)); [reflexivity|reflexivity| |].
 { intros x'. apply (thr (S j) w' K0 K s0 s HK HS []); [reflexivity|lia]. }
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Ret v) (KLet x b rho :: K) s)); [reflexivity|apply KB.sval_next; cbn; exact Ey| |].
 { intros x'. apply (thr (S (S j)) w' K0 K s0 s HK HS [KLet x b rho]); [reflexivity|lia]. }
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval ((x, v) :: rho) b) K s)); [reflexivity|reflexivity| |].
 { intros x'. apply (thr (S (S (S j))) w' K0 K s0 s HK HS [KLet x b rho]); [reflexivity|lia]. }
 eapply KB.ObsT_anti.
 { apply (KB.srun_tau sealed _ (Cfg (Eval rho0 a) (KLet x b0 rho0 :: K0) s0)); [reflexivity|].
   change (@nil event) with (@nil event ++ @nil event). eapply KB.srun_trans.
   - apply (src_path a x1 ops rho0 vx v0 _ s0 Hp Ex Ev0). eapply hd_tl_src; exact HS.
   - apply (KB.srun_tau sealed _ (Cfg (Eval ((x, v0) :: rho0) b0) K0 s0)); [reflexivity|apply KB.srun_refl]. }
 assert (Hi' : ThenInv j w' (x :: g) ((x, p) :: fdrop x Ps) ((x, p) :: fdrop x Pt) ((x, v0) :: rho0) ((x, v) :: rho)).
 { destruct (ThenInv_mono k j w w' g Ps Pt rho0 rho ltac:(lia) W Hi) as (Wf & HE & HFs & HFt).
   split; [exact Wf|split; [apply EnvRel_cons_same'; [eapply KB.VRel_mono; [|exact W|exact HV]; lia|exact HE]|split]].
   - destruct p as [pb pops0]. eapply FactsAll_add; [exact HFs|exact Eb0|exact Ep0|exact Tx].
   - destruct p as [pb pops0]. eapply FactsAll_add; [exact HFt|exact Eb|exact Ep|exact Tx]. }
 eapply KB.ERel_apply; [apply (Hb j w' v0 v); [lia|exact W|exact Hi']|apply le_n|eapply KB.wext_self; exact HS| |].
 - eapply KB.KRel_down; [|exact HK]; lia.
 - eapply KB.SRel_down; [|exact HS]; lia.
Qed.

Lemma fund_below_all : forall k, JitKRef.JitKRef.fund_below sealed D k.
Proof.
 intros k. apply (JitKRefFund.JitKRefFund.fund_below_le sealed D (S k) k (Nat.le_succ_diag_r k)).
 exact (JitKRefFund.JitKRefFund.fund_gen sealed D Dw k).
Qed.

Lemma then_head : forall rec, chk_sound rec -> forall X X' g Ps Pt k w rho0 rho,
 (rec g X X' || reuse_var g Ps Pt X X') = true -> ThenInv k w g Ps Pt rho0 rho -> ERel k w rho0 X rho X'.
Proof.
 intros rec Hr X X' g Ps Pt k w rho0 rho E Hi. apply orb_true_iff in E as [E|E].
 - destruct Hi as (Wf & HE & _). exact (Hr g X X' E k w rho0 rho Wf HE).
 - unfold reuse_var in E. destruct (reuse_path g Ps Pt X X') as [p|] eqn:Ep; [|discriminate].
   destruct X' as [| | | | | y | | | | | | | | | | | |]; try (cbn in Ep; discriminate).
   exact (ERel_reuse_var k w g Ps Pt rho0 rho X y p Hi Ep).
Qed.

Theorem then_sound : forall rec, chk_sound rec -> forall X X' g Ps Pt, then_chk rec g Ps Pt X X' = true ->
 forall k w rho0 rho, ThenInv k w g Ps Pt rho0 rho -> ERel k w rho0 X rho X'.
Proof.
 intros rec Hr X. induction X using expr_ind'; intros X' g Ps Pt E k w rho0 rho Hi.
 all: match goal with |- ERel _ _ _ ?Xe _ _ =>
   destruct (rec g Xe X' || reuse_var g Ps Pt Xe X') eqn:Eh; [exact (then_head rec Hr Xe X' g Ps Pt k w rho0 rho Eh Hi)|] end.
 all: cbn [then_chk] in E; rewrite Eh in E; cbn [orb] in E; try discriminate.
 - (* let *)
   match goal with |- ERel _ _ _ (ELet ?x ?a ?b) _ _ => rename x into lx, a into la, b into lb end.
   match goal with H : forall X' g Ps Pt, then_chk rec g Ps Pt la X' = true -> _ |- _ => rename H into IHa end.
   match goal with H : forall X' g Ps Pt, then_chk rec g Ps Pt lb X' = true -> _ |- _ => rename H into IHb end.
   destruct X' as [| | | | | | | x' a' b' | | | | | | | | | |]; try discriminate.
   apply andb_true_iff in E as [Ex E]. apply text_eqb_eq in Ex. subst x'. apply orb_true_iff in E as [E|E].
   + destruct (reuse_path g Ps Pt la a') as [p|] eqn:Er; [|discriminate].
     apply andb_true_iff in E as [Tx E]. apply negb_true_iff in Tx.
     destruct a' as [| | | | | y | | | | | | | | | | | |]; try (cbn in Er; discriminate).
     eapply ERel_reuse_let; [exact Hi|exact Er|exact Tx|].
     intros j w' v0 v L W Hi'. exact (IHb b' _ _ _ E j w' _ _ Hi').
   + apply andb_true_iff in E as [Ea Eb].
     apply (JitKRefCompatCtl.JitKRefCompatCtl.ERel_let sealed D); [exact (IHa a' g Ps Pt Ea k w rho0 rho Hi)|].
     intros j w' v0 v L W HV. apply (IHb b' (lx :: g) (fdrop lx Ps) (fdrop lx Pt) Eb j w').
     destruct (ThenInv_mono k j w w' g Ps Pt rho0 rho L W Hi) as (Wf & HE & HFs & HFt).
     split; [exact Wf|split; [apply EnvRel_cons_same'; [exact HV|exact HE]|split; apply FactsAll_drop; assumption]].
 - (* named call *)
   match goal with |- ERel _ _ _ (ECall ?f ?l) _ _ => rename f into cf, l into cl end.
   match goal with H : Forall _ cl |- _ => rename H into Fl end.
   destruct X' as [| | | | | | | | | | | | | | | | | f' l']; try discriminate.
   apply andb_true_iff in E as [Ef E]. apply text_eqb_eq in Ef. subst f'.
   apply (JitKRefCompatCall.JitKRefCompatCall.compat_call_core sealed D k w rho0 cf cl rho l' (fund_below_all k)
     (JitKRefPrim.JitKRefPrim.prim_compat sealed D)).
   clear Eh. revert l' E. induction Fl as [|a l Ha F IH]; intros [|b l'] E; cbn in E; try discriminate; [constructor|].
   apply andb_true_iff in E as [E1 E2]. constructor.
   + intros j w' L W. exact (Ha b g Ps Pt E1 j w' rho0 rho (ThenInv_mono k j w w' g Ps Pt rho0 rho ltac:(lia) W Hi)).
   + exact (IH l' E2).
Qed.

Definition CRel (k : nat) (w : world) (X Y : expr) (rho0 rho0i : lenv) (C : expr) (rhoi : lenv) (U : expr)
  (m : nat) : Prop :=
 forall j w' K0 K s0 s, (j <= k)%nat -> wext w w' -> KRel j w' K0 K -> SRel j w' s0 s ->
  ObsT j w' (Cfg (Eval rho0i C) (andRs m ++ KIf X Y rho0 :: K0) s0) (Cfg (Eval rhoi U) K s).

Section Chain.
Variable rec : list name -> expr -> expr -> bool.
Hypothesis Hr : chk_sound rec.
Variables (g0 : list name) (G : name) (X Y Y' : expr) (rT rho0 : lenv).

(* Pt: the target facts the chain has recorded so far, each over a variable of g0. *)
Definition chain_hyps (k : nat) (w : world) (Pt : facts) (g : list name) (rho0i rhoi : lenv) : Prop :=
 wf_world w /\ EnvRel_with (VRel k) w g rho0i rhoi /\ EnvRel_with (VRel k) w g0 rho0 rhoi /\
 lookup G rhoi = Some (VFrozen Y' rT) /\ ERel k w rho0 Y rT Y' /\
 FactsAll Pt rhoi /\ (forall y p, In (y, p) Pt -> In (fst p) g0).

Lemma chain_hyps_mono : forall k j w w' Pt g r0 r, (j <= k)%nat -> wext w w' -> chain_hyps k w Pt g r0 r -> chain_hyps j w' Pt g r0 r.
Proof.
 intros k j w w' Pt g r0 r L W (Wf & H1 & H2 & H3 & H4 & H5 & H6). split; [exact (proj2 W)|].
 split; [eapply KB.EnvRel_mono; eauto|split; [eapply KB.EnvRel_mono; eauto|split; [exact H3|split; [eapply KB.ERel_mono; eauto|auto]]]].
Qed.

Lemma thaw_from_hyps : forall k w Pt g r0 r, chain_hyps k w Pt g r0 r ->
 forall j w', (j <= k)%nat -> wext w w' -> ERel j w' rho0 Y r (thaw_e G).
Proof.
 intros k w Pt g r0 r (Wf & H1 & H2 & H3 & H4 & _) j w' L W. eapply thaw_erel; [exact H3|]. eapply KB.ERel_mono; eauto.
Qed.

Lemma then_from_hyps : forall k w Pt g r0 r X', then_chk rec g0 [] Pt X X' = true -> chain_hyps k w Pt g r0 r ->
 forall j w', (j <= k)%nat -> wext w w' -> ERel j w' rho0 X r X'.
Proof.
 intros k w Pt g r0 r X' E (Wf & H1 & H2 & H3 & H4 & H5 & H6) j w' L W. apply (then_sound rec Hr X X' g0 [] Pt E).
 split; [exact (proj2 W)|split; [eapply KB.EnvRel_mono; eauto|split; [apply FactsAll_nil|exact H5]]].
Qed.

Lemma is_thaw_of_eq : forall Z, is_thaw_of G Z = true -> Z = thaw_e G.
Proof.
 intros Z E. destruct Z as [| | | | | | | | | | | | | | | | | f args]; try (cbn in E; discriminate).
 destruct args as [|a l]; try (cbn in E; discriminate).
 destruct a as [| | | | | x | | | | | | | | | | | |]; try (cbn in E; discriminate).
 destruct l as [|b l]; [|cbn in E; discriminate].
 cbn in E. apply andb_true_iff in E as [E1 E2].
 apply text_eqb_eq in E1. apply text_eqb_eq in E2. subst. reflexivity.
Qed.

(* Throws while the target runs ahead of a source that is still at the chain's node. *)
Lemma chain_thr : forall j w' m K0 K s0 s Fs x, KRel j w' K0 K -> SRel j w' s0 s -> forallb KB.nontrap Fs = true ->
 forall i, (i <= j)%nat -> ObsT i w' (Cfg (Throw x) (andRs m ++ KIf X Y rho0 :: K0) s0) (Cfg (Throw x) (Fs ++ K) s).
Proof.
 intros j w' m K0 K s0 s Fs x HK HS N i L. rewrite stack_eq.
 apply (throw_pop j w' K0 K (andRs m ++ [KIf X Y rho0]) Fs); [exact HK|apply nontrap_andRs; reflexivity|exact N|exact L|eapply KB.wext_self; exact HS|].
 eapply KB.SRel_down; [|exact HS]; exact L.
Qed.

Lemma chain_base : forall k w m Pt g rho0i rhoi C U, chain_hyps k w Pt g rho0i rhoi ->
 base_chk rec g0 Pt G X g C U = true -> CRel k w X Y rho0 rho0i C rhoi U m.
Proof.
 intros k w m Pt g rho0i rhoi C U Hh E. unfold base_chk in E. destruct U as [| | | | | | | | U1 U2 U3 | | | | | | | | |]; try discriminate.
 apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2]. apply is_thaw_of_eq in E1. subst U3.
 intros j w' K0 K s0 s L W HK HS. destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval rhoi U1) (KIf U2 (thaw_e G) rhoi :: K) s)); [reflexivity|reflexivity| |].
 - intros x. cbn [kont mem]. apply (chain_thr (S j) w' m K0 K s0 s [] x HK HS); [reflexivity|lia].
 - assert (Hj : chain_hyps j w' Pt g rho0i rhoi) by (eapply chain_hyps_mono; [|exact W|exact Hh]; lia).
   pose proof Hj as Hjj. destruct Hj as (Wf & HE & HE0 & HG & HY & _).
   eapply KB.ERel_apply; [apply (Hr g C U1 E2); [exact Wf|exact HE]|apply le_n|eapply KB.wext_self; exact HS| |].
   + apply kif_base; [eapply KB.KRel_down; [|exact HK]; lia| |].
     * intros j' w'' L' W'. eapply then_from_hyps; [exact E3|exact Hjj|exact L'|exact W'].
     * intros j' w'' L' W'. eapply thaw_from_hyps; [exact Hjj|exact L'|exact W'].
   + eapply KB.SRel_down; [|exact HS]; lia.
Qed.

Lemma chain_and : forall k w m Pt g rho0i rhoi T Sc U1 T' Z,
 chain_hyps k w Pt g rho0i rhoi -> is_thaw_of G Z = true -> rec g T T' = true ->
 CRel k w X Y rho0 rho0i Sc rhoi U1 (S m) ->
 CRel k w X Y rho0 rho0i (EAnd T Sc) rhoi (EIf T' U1 Z) m.
Proof.
 intros k w m Pt g rho0i rhoi T Sc U1 T' Z Hh Ez Et IH. apply is_thaw_of_eq in Ez. subst Z.
 intros j w' K0 K s0 s L W HK HS. destruct j as [|j]; [apply KB.ObsT_0|].
 apply KB.ObsT_running; [reflexivity|unfold KB.nonterm; cbn; exact I| | |].
 - intros x. cbn [kont mem]. apply (chain_thr (S j) w' m K0 K s0 s [] x HK HS); [reflexivity|lia].
 - intros c1 E1. cbn in E1. injection E1 as <-.
   exists (Cfg (Eval rho0i T) (KAnd Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) s0).
   split; [eapply KB.srun_tau; [reflexivity|apply KB.srun_refl]|].
   assert (Hj : chain_hyps j w' Pt g rho0i rhoi) by (eapply chain_hyps_mono; [|exact W|exact Hh]; lia).
   pose proof Hj as Hjj. destruct Hj as (Wf & HE & HE0 & HG & HY & _).
   eapply KB.ERel_apply; [apply (Hr g T T' Et); [exact Wf|exact HE]|apply le_n|eapply KB.wext_self; exact HS| |].
   + apply kand_frame; [eapply KB.KRel_down; [|exact HK]; lia| |].
     * intros j' w'' L' W'. eapply thaw_from_hyps; [exact Hjj|exact L'|exact W'].
     * intros j' w'' s0' s' L' W' HS'. apply (IH j' w'' K0 K s0' s'); [lia|eapply KB.wext_trans; [exact W|exact W']| |exact HS'].
       eapply KB.KRel_mono; [|exact W'|exact HK]. lia.
   + eapply KB.SRel_down; [|exact HS]; lia.
 - intros q kk r E1. cbn in E1. discriminate.
Qed.

(* A chain let whose expression is checked by rec only: the binder's facts are dropped. *)
Lemma chain_let : forall k w m Pt g rho0i rhoi x E Sc E' U1,
 chain_hyps k w Pt g rho0i rhoi -> bound g0 x = false -> text_eqb x G = false -> rec g E E' = true ->
 (forall k' w' v0 v, (k' <= k)%nat -> wext w w' -> chain_hyps k' w' (fdrop x Pt) (x :: g) ((x, v0) :: rho0i) ((x, v) :: rhoi) ->
    CRel k' w' X Y rho0 ((x, v0) :: rho0i) Sc ((x, v) :: rhoi) U1 m) ->
 CRel k w X Y rho0 rho0i (ELet x E Sc) rhoi (ELet x E' U1) m.
Proof.
 intros k w m Pt g rho0i rhoi x E Sc E' U1 Hh Bx Gx Ee IH.
 intros j w' K0 K s0 s L W HK HS. destruct j as [|j]; [apply KB.ObsT_0|].
 apply KB.ObsT_running; [reflexivity|unfold KB.nonterm; cbn; exact I| | |].
 - intros x'. cbn [kont mem]. apply (chain_thr (S j) w' m K0 K s0 s [] x' HK HS); [reflexivity|lia].
 - intros c1 E1. cbn in E1. injection E1 as <-.
   exists (Cfg (Eval rho0i E) (KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) s0).
   split; [eapply KB.srun_tau; [reflexivity|apply KB.srun_refl]|].
   assert (Hj : chain_hyps j w' Pt g rho0i rhoi) by (eapply chain_hyps_mono; [|exact W|exact Hh]; lia).
   pose proof Hj as Hjj. destruct Hj as (Wf & HE & HE0 & HG & HY & _).
   eapply KB.ERel_apply; [apply (Hr g E E' Ee); [exact Wf|exact HE]|apply le_n|eapply KB.wext_self; exact HS| |].
   + change (KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) with ([KLet x Sc rho0i] ++ andRs m ++ KIf X Y rho0 :: K0).
     rewrite stack_eq, app_assoc.
     apply krel_build; [eapply KB.KRel_down; [|exact HK]; lia|cbn; apply nontrap_andRs; reflexivity|reflexivity| |].
     * intros j' w'' v0 v s0' s' c1 L' W' HV HS' E2. cbn in E2. injection E2 as <-.
       rewrite <- app_assoc, <- stack_eq. cbn [app].
       eexists; split; [eapply KB.srun_tau; [reflexivity|apply KB.srun_refl]|].
       assert (Hx : chain_hyps j' w'' (fdrop x Pt) (x :: g) ((x, v0) :: rho0i) ((x, v) :: rhoi)).
       { destruct (chain_hyps_mono j j' w' w'' Pt g rho0i rhoi ltac:(lia) W' Hjj) as (Wf' & HE' & HE0' & HG' & HY' & HF' & HB').
         split; [exact Wf'|split; [|split; [|split; [|split; [exact HY'|split]]]]].
         - apply EnvRel_cons_same; [eapply KB.VRel_down; [|exact HV]; lia|exact HE'].
         - apply EnvRel_cons_r; [apply bound_false; exact Bx|exact HE0'].
         - cbn. rewrite text_eqb_neq in Gx. destruct (text_eqb G x) eqn:T; [|exact HG'].
           apply text_eqb_eq in T. subst. contradiction.
         - apply FactsAll_drop. exact HF'.
         - intros y p I. apply fdrop_in in I as (I & _). exact (HB' y p I). }
       pose proof (IH j' w'' v0 v ltac:(lia) (KB.wext_trans _ _ _ W W') Hx) as Hc.
       apply (Hc j' w'' K0 K s0' s'); [apply le_n|eapply KB.wext_self; exact HS'| |].
       -- eapply KB.KRel_mono; [|exact W'|exact HK]. lia.
       -- eapply KB.SRel_down; [|exact HS']; lia.
     * intros v s'. eexists. reflexivity.
   + eapply KB.SRel_down; [|exact HS]; lia.
 - intros q kk r E1. cbn in E1. discriminate.
Qed.

(* A chain let of (hd y) or (tl y): both sides run the same three steps (the call's frame, y, the
   primitive), on related values, so they bind related values or raise the same XPrim; the target's
   value is the path's, which is the fact recorded. *)
Lemma chain_let_path : forall k w m Pt g rho0i rhoi x (o : bool) y Sc U1 b ops,
 chain_hyps k w Pt g rho0i rhoi -> bound g0 x = false -> text_eqb x G = false -> In y g -> In b g0 ->
 (forall vy, lookup y rhoi = Some vy -> exists vb, lookup b rhoi = Some vb /\ pops vb ops = Some vy) ->
 (forall k' w' v0 v, (k' <= k)%nat -> wext w w' ->
    chain_hyps k' w' ((x, (b, ops ++ [o])) :: fdrop x Pt) (x :: g) ((x, v0) :: rho0i) ((x, v) :: rhoi) ->
    CRel k' w' X Y rho0 ((x, v0) :: rho0i) Sc ((x, v) :: rhoi) U1 m) ->
 CRel k w X Y rho0 rho0i (ELet x (ECall (if o then hd_name else tl_name) [EVar y]) Sc) rhoi
   (ELet x (ECall (if o then hd_name else tl_name) [EVar y]) U1) m.
Proof.
 intros k w m Pt g rho0i rhoi x o y Sc U1 b ops Hh Bx Gx Iy Ib Hb IH.
 set (f := if o then hd_name else tl_name). set (E := ECall f [EVar y]).
 intros j w' K0 K s0 s L W HK HS.
 destruct (chain_hyps_mono k j w w' Pt g rho0i rhoi L W Hh) as (Wf & HE & HE0 & HG & HY & HF & HB).
 destruct (HE y Iy) as (vy0 & vy & Ey0 & Ey & HVy).
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval rhoi E) (KLet x U1 rhoi :: K) s)); [reflexivity|reflexivity| |].
 { intros x'. cbn [kont mem]. apply (chain_thr (S j) w' m K0 K s0 s [] x' HK HS); [reflexivity|lia]. }
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval rhoi (EVar y)) (KCallArgs f [] [] rhoi :: KLet x U1 rhoi :: K) s)); [reflexivity|reflexivity| |].
 { intros x'. cbn [kont mem]. apply (chain_thr (S (S j)) w' m K0 K s0 s [KLet x U1 rhoi] x' HK HS); [reflexivity|lia]. }
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Ret vy) (KCallArgs f [] [] rhoi :: KLet x U1 rhoi :: K) s)); [reflexivity|apply KB.sval_next; cbn; exact Ey| |].
 { intros x'. cbn [kont mem]. apply (chain_thr (S (S (S j))) w' m K0 K s0 s [KCallArgs f [] [] rhoi; KLet x U1 rhoi] x' HK HS); [reflexivity|lia]. }
 assert (Hs : hd_tl s) by (eapply hd_tl_tgt; exact HS). assert (Hs0 : hd_tl s0) by (eapply hd_tl_src; exact HS).
 (* the source, up to its Ret at the call frame *)
 assert (Src : srun (Cfg (Eval rho0i (ELet x E Sc)) (andRs m ++ KIf X Y rho0 :: K0) s0) []
   (Cfg (Ret vy0) (KCallArgs f [] [] rho0i :: KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) s0)).
 { apply (KB.srun_tau sealed _ (Cfg (Eval rho0i E) (KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) s0)); [reflexivity|].
   apply (KB.srun_tau sealed _ (Cfg (Eval rho0i (EVar y)) (KCallArgs f [] [] rho0i :: KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) s0)); [reflexivity|].
   eapply KB.srun_tau; [apply KB.sval_next; cbn; exact Ey0|apply KB.srun_refl]. }
 pose proof (VRel_pop o (S (S (S j))) w' vy0 vy HVy) as Hp.
 destruct (pop o vy) as [v|] eqn:Ev; destruct (pop o vy0) as [v0|] eqn:Ev0; try contradiction.
 - destruct j as [|j]; [apply KB.ObsT_0|].
   apply (tgt_tau _ _ _ _ (Cfg (Ret v) (KLet x U1 rhoi :: K) s)); [reflexivity|unfold f; rewrite (prim_pop_next o vy rhoi _ s Hs), Ev; reflexivity| |].
   { intros x'. cbn [kont mem]. apply (chain_thr (S (S (S (S j)))) w' m K0 K s0 s [KCallArgs f [] [] rhoi; KLet x U1 rhoi] x' HK HS); [reflexivity|lia]. }
   destruct j as [|j]; [apply KB.ObsT_0|].
   apply (tgt_tau _ _ _ _ (Cfg (Eval ((x, v) :: rhoi) U1) K s)); [reflexivity|reflexivity| |].
   { intros x'. cbn [kont mem]. apply (chain_thr (S (S (S (S (S j))))) w' m K0 K s0 s [KLet x U1 rhoi] x' HK HS); [reflexivity|lia]. }
   eapply KB.ObsT_anti.
   { change (@nil event) with (@nil event ++ @nil event). eapply KB.srun_trans; [exact Src|].
     eapply KB.srun_tau; [unfold f; rewrite (prim_pop_next o vy0 rho0i _ s0 Hs0), Ev0; reflexivity|].
     apply (KB.srun_tau sealed _ (Cfg (Eval ((x, v0) :: rho0i) Sc) (andRs m ++ KIf X Y rho0 :: K0) s0)); [reflexivity|apply KB.srun_refl]. }
   assert (Hx : chain_hyps j w' ((x, (b, ops ++ [o])) :: fdrop x Pt) (x :: g) ((x, v0) :: rho0i) ((x, v) :: rhoi)).
   { destruct (chain_hyps_mono k j w w' Pt g rho0i rhoi ltac:(lia) W Hh) as (Wf' & HE' & HE0' & HG' & HY' & HF' & HB').
     assert (Tbx : text_eqb b x = false).
     { apply Bool.not_true_iff_false. intro T. apply text_eqb_eq in T. subst b. apply (bound_false g0 x Bx). exact Ib. }
     split; [exact Wf'|split; [|split; [|split; [|split; [exact HY'|split]]]]].
     - apply EnvRel_cons_same; [|exact HE']. eapply KB.VRel_down; [|exact Hp]. lia.
     - apply EnvRel_cons_r; [apply bound_false; exact Bx|exact HE0'].
     - cbn. rewrite text_eqb_neq in Gx. destruct (text_eqb G x) eqn:T; [|exact HG'].
       apply text_eqb_eq in T. subst. contradiction.
     - destruct (Hb vy Ey) as (vb & Eb & Ep). eapply FactsAll_add; [exact HF'|exact Eb| |exact Tbx].
       rewrite pops_app, Ep. cbn. rewrite Ev. reflexivity.
     - intros y' p [Ey'|I]; [injection Ey' as <- <-; exact Ib|]. apply fdrop_in in I as (I & _). exact (HB' y' p I). }
   apply (IH j w' v0 v ltac:(lia) W Hx j w' K0 K s0 s (le_n _) (KB.wext_self sealed D _ _ _ _ HS)).
   + eapply KB.KRel_down; [|exact HK]; lia.
   + eapply KB.SRel_down; [|exact HS]; lia.
 - (* hd or tl of a non-pair: both raise XPrim *)
   destruct j as [|j]; [apply KB.ObsT_0|].
   apply (tgt_tau _ _ _ _ (Cfg (Throw (XPrim (if o then PHd else PTl))) (KLet x U1 rhoi :: K) s));
    [reflexivity|unfold f; rewrite (prim_pop_next o vy rhoi _ s Hs), Ev; reflexivity| |].
   { intros x'. cbn [kont mem]. apply (chain_thr (S (S (S (S j)))) w' m K0 K s0 s [KCallArgs f [] [] rhoi; KLet x U1 rhoi] x' HK HS); [reflexivity|lia]. }
   eapply KB.ObsT_anti.
   { change (@nil event) with (@nil event ++ @nil event). eapply KB.srun_trans; [exact Src|].
     eapply KB.srun_tau; [unfold f; rewrite (prim_pop_next o vy0 rho0i _ s0 Hs0), Ev0; reflexivity|apply KB.srun_refl]. }
   change (KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) with ([KLet x Sc rho0i] ++ andRs m ++ KIf X Y rho0 :: K0).
   rewrite stack_eq, app_assoc.
   apply (throw_pop (S (S (S (S j)))) w' K0 K ([KLet x Sc rho0i] ++ andRs m ++ [KIf X Y rho0]) [KLet x U1 rhoi]);
    [exact HK|cbn; apply nontrap_andRs; reflexivity|reflexivity|lia|eapply KB.wext_self; exact HS|].
   eapply KB.SRel_down; [|exact HS]; lia.
Qed.

(* What chain_fact recorded: nothing new (the binder's facts dropped), or the path fact of a let
   of (hd y) or (tl y). *)
Lemma chain_fact_cases : forall g Pt x E E', chain_fact g g0 Pt x E E' = fdrop x Pt \/
 exists (o : bool) y b ops, E = ECall (if o then hd_name else tl_name) [EVar y] /\ E' = E /\ In y g /\
   chain_fact g g0 Pt x E E' = (x, (b, ops ++ [o])) :: fdrop x Pt /\
   ((flookup y Pt = Some (b, ops)) \/ (b = y /\ ops = [] /\ In y g0)).
Proof.
 intros g Pt x E E'. unfold chain_fact.
 destruct E as [| | | | | | | | | | | | | | | | | f args]; try (left; reflexivity).
 destruct args as [|a [|a2 args]]; try (left; reflexivity); [|left; destruct a; reflexivity].
 destruct a as [| | | | | y | | | | | | | | | | | |]; try (left; reflexivity).
 destruct (op_of f) as [o|] eqn:Eo; [|left; reflexivity].
 destruct (expr_eqb (ECall f [EVar y]) E' && bound g y) eqn:B; [|left; reflexivity].
 apply andb_true_iff in B as [B1 B2]. apply expr_eqb_eq in B1. apply bound_in in B2.
 rewrite (op_of_some f o Eo) in *.
 destruct (flookup y Pt) as [[b ops]|] eqn:Fl.
 - right. exists o, y, b, ops. split; [reflexivity|split; [symmetry; exact B1|split; [exact B2|split; [reflexivity|left; exact Fl]]]].
 - destruct (bound g0 y) eqn:B0; [|left; reflexivity].
   right. exists o, y, y, []. split; [reflexivity|split; [symmetry; exact B1|split; [exact B2|split; [reflexivity|]]]].
   right. split; [reflexivity|split; [reflexivity|apply bound_in; exact B0]].
Qed.

Theorem chain_sound : forall C k w m Pt g rho0i rhoi U, chain_hyps k w Pt g rho0i rhoi ->
 chain_chk rec g0 Pt G X g C U = true -> CRel k w X Y rho0 rho0i C rhoi U m.
Proof.
 induction C; intros k w m Pt g rho0i rhoi U Hh E; cbn [chain_chk] in E;
  (apply orb_true_iff in E as [E|E]; [eapply chain_base; eassumption|]); try (destruct U; discriminate).
 - (* let *) destruct U as [| | | | | | | x' E' U1 | | | | | | | | | |]; try discriminate.
   apply andb_true_iff in E as [E EC]. apply andb_true_iff in E as [E Ee].
   apply andb_true_iff in E as [E Gx]. apply andb_true_iff in E as [E Bx]. apply text_eqb_eq in E. subst x'.
   apply negb_true_iff in Gx, Bx.
   match goal with |- CRel _ _ _ _ _ _ (ELet ?lx ?lE _) _ _ _ => rename lx into cx, lE into cE end.
   destruct (chain_fact_cases g Pt cx cE E') as [Ef|(o & y & b & ops & -> & -> & Iy & Ef & Hf)]; rewrite Ef in EC.
   + eapply chain_let; [exact Hh|exact Bx|exact Gx|exact Ee|].
     intros k' w' v0 v L W Hx. eapply IHC2; [exact Hx|exact EC].
   + apply (chain_let_path k w m Pt g rho0i rhoi cx o y C2 U1 b ops); [exact Hh|exact Bx|exact Gx|exact Iy| | |].
     * destruct Hf as [Hf|(-> & -> & I0)]; [|exact I0].
       destruct Hh as (_ & _ & _ & _ & _ & _ & HB). exact (HB y (b, ops) (flookup_in _ _ _ Hf)).
     * intros vy Ey. destruct Hf as [Hf|(-> & -> & _)]; [|exists vy; split; [exact Ey|reflexivity]].
       destruct Hh as (_ & _ & _ & _ & _ & HF & _). destruct (HF y (b, ops) (flookup_in _ _ _ Hf)) as (v & vb & E1 & E2 & E3).
       rewrite Ey in E1. injection E1 as <-. exists vb. split; assumption.
     * intros k' w' v0 v L W Hx. eapply IHC2; [exact Hx|exact EC].
 - (* and *) destruct U as [| | | | | | | | T' U1 Z | | | | | | | | |]; try discriminate.
   repeat (apply andb_true_iff in E as [E ?]).
   eapply chain_and; [exact Hh|exact E|eassumption|]. eapply IHC2; [exact Hh|eassumption].
Qed.
End Chain.

Theorem share_rule_sound : rule_sound share_rule.
Proof.
 intros rec Hr g e0 e E. unfold share_rule in E.
 destruct e0 as [| | | | | | | | C X Y | | | | | | | | |]; try discriminate.
 destruct e as [| | | | | | | G A U | | | | | | | | | |]; try discriminate.
 destruct A as [| | | | | | | | | | | | | Y' | | | |]; try discriminate. repeat (apply andb_true_iff in E as [E ?]).
 rename E into BG. apply negb_true_iff, bound_false in BG.
 match goal with B : negb (bound g id_key) = true |- _ => apply negb_true_iff, bound_false in B; rename B into BI end.
 match goal with B : rec g Y Y' = true |- _ => rename B into EY end.
 match goal with B : chain_chk rec g [] G X g C U = true |- _ => rename B into EC end.
 intros k w rho0 rho Wf0 HE. apply KB.ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply KB.ObsT_running; [reflexivity|unfold KB.nonterm; cbn; exact I| | |].
 - intros x. apply (KB.KRel_throw sealed D); [eapply KB.KRel_down; [|exact HK]; lia|eapply KB.SRel_down; [|exact HS]; lia].
 - intros c1 E1. cbn in E1. injection E1 as <-.
   exists (Cfg (Eval rho0 C) (KIf X Y rho0 :: K0) s0). split; [eapply KB.srun_tau; [reflexivity|apply KB.srun_refl]|].
   set (fr := VFrozen Y' (tagged_env rho s)).
   destruct j as [|j]; [apply KB.ObsT_0|].
   apply (tgt_tau _ _ _ _ (Cfg (Ret fr) (KLet G U rho :: K) (with_cell s))); [reflexivity|reflexivity| |].
   { intros x. apply (throw_pop (S (S j)) w' K0 K [KIf X Y rho0] [KLet G U rho]); [exact HK|reflexivity|reflexivity|lia|eapply KB.wext_self; exact HS|].
     eapply KB.SRel_down; [|exact HS]; lia. }
   destruct j as [|j]; [apply KB.ObsT_0|].
   apply (tgt_tau _ _ _ _ (Cfg (Eval ((G, fr) :: rho) U) K (with_cell s))); [reflexivity|reflexivity| |].
   { intros x. apply (throw_pop (S (S (S j))) w' K0 K [KIf X Y rho0] [KLet G U rho]); [exact HK|reflexivity|reflexivity|lia|eapply KB.wext_self; exact HS|].
     apply SRel_with_cell_tgt. eapply KB.SRel_down; [|exact HS]; lia. }
   assert (Wf' : wf_world w') by exact (proj2 W).
   assert (HE' : EnvRel_with (VRel j) w' g rho0 rho) by (eapply KB.EnvRel_mono; [|exact W|exact HE]; lia).
   assert (Hh : chain_hyps g G Y Y' (tagged_env rho s) rho0 j w' [] g rho0 ((G, fr) :: rho)).
   { split; [exact Wf'|split; [apply EnvRel_cons_r; assumption|split; [apply EnvRel_cons_r; assumption|split; [|split; [|split; [apply FactsAll_nil|intros y p []]]]]]].
     - cbn [lookup]. rewrite text_eqb_refl. reflexivity.
     - apply (Hr g Y Y' EY); [exact Wf'|]. unfold tagged_env. apply EnvRel_cons_r; assumption. }
   apply (chain_sound rec Hr g G X Y Y' (tagged_env rho s) rho0 C j w' 0 [] g rho0 ((G, fr) :: rho) U Hh EC j w' K0 K s0 (with_cell s));
    [apply le_n|eapply KB.wext_self; exact HS| |].
   + eapply KB.KRel_down; [|exact HK]; lia.
   + apply SRel_with_cell_tgt. eapply KB.SRel_down; [|exact HS]; lia.
 - intros q kk r E1. cbn in E1. discriminate.
Qed.

Theorem share_rules_sound : Forall rule_sound share_rules.
Proof. constructor; [exact share_rule_sound|constructor]. Qed.

(* check_share is sound under FrontHyps and thaw's definition in D. *)
(* check_share is sound for every D_wf D (Dw) in which thaw is the kernel's (HT) and hd and tl are
   the primitives (HP), the Section hypotheses above. FrontHyps is no longer a premise: front_hyps
   derives it from D_wf. *)
Theorem check_share_sound : forall ps b0 b, check_share ps b0 b = true -> KRef ps b0 b.
Proof. intros ps b0 b E. exact (fchk_sound sealed D (front_hyps sealed D Dw) share_rules share_rules_sound _ ps b0 b E). Qed.
End Share.

(* A pair judge_share accepts is a definition and its share witness of the same name and
   parameters whose bodies are in KRef, for every D meeting check_share_sound's premises. *)
Theorem judge_share_sound : forall form share f, judge_share form share = SAccepted f ->
 exists ps b0 b, parse [] (to_value form) = Some (EDefun f ps b0) /\ parse [] (to_value share) = Some (EDefun f ps b) /\
 forall sealed D tp, In (thaw_name, FUser [tp] (EApp (EVar tp) [])) D ->
  In (hd_name, FPrim PHd) D /\ In (tl_name, FPrim PTl) D -> JitKRef.JitKRef.D_wf sealed D ->
  JitKRef.JitKRef.KRef sealed D ps b0 b.
Proof.
 intros form share f E. unfold judge_share in E.
 destruct (parse [] (to_value form)) as [e0|] eqn:E1; destruct (parse [] (to_value share)) as [e|] eqn:E2; try discriminate;
  destruct e0 as [| | | | | | | | | | | | | | | g0 qs0 c0 | |]; try discriminate;
  destruct e as [| | | | | | | | | | | | | | | g1 qs1 c1 | |]; try discriminate.
 destruct (text_eqb g0 g1 && forall2b text_eqb qs0 qs1) eqn:Ep; [|discriminate].
 destruct (check_share qs0 c0 c1) eqn:Ec; [|discriminate]. injection E as <-.
 apply andb_true_iff in Ep as [Ef Eps]. apply text_eqb_eq in Ef. apply text_list_eq in Eps. subst g1 qs1.
 exists qs0, c0, c1. split; [reflexivity|split; [reflexivity|]].
 intros sealed D tp HT HP Dw. exact (check_share_sound sealed D tp HT HP Dw qs0 c0 c1 Ec).
Qed.

(* HP is what any store of call_preservation_src meets: Com's FunRel gives every primitive name
   its primitive (fr_name), so a store with Com s m holds D_hp, hd and tl as the primitives. *)
Theorem hp_of_com : forall s m, JitLowerStep.JitLowerStep.Com s m -> JitKRef.JitKRef.StoreHas D_hp s.
Proof.
 intros s m [_ F] f d [E|[E|[]]]; injection E as <- <-; apply (JitLowerStep.JitLowerStep.fr_name s m F); vm_compute; reflexivity.
Qed.

(* ---------- a literal refines itself, for every D ----------
   Proved directly (one tau step to Ret on each side, then the continuations' Ret clause), with no
   FrontHyps premise: the counterexample below uses it so that it needs no KRef_refl. *)
Section Lit.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).

Lemma lit_vrel : forall e v k w, lit_val e = Some v -> VRel k w v v.
Proof.
 intros e v k w H. rewrite (JitKRefGround.JitKRefGround.VRel_unfold sealed D k).
 destruct e; cbn in H; try discriminate; injection H as <-; cbn; reflexivity || exact I.
Qed.

Theorem lit_kref : forall g e v, lit_val e = Some v -> KRef g e e.
Proof.
 intros g e v Hl k w rho0 rho _ _. apply KB.ERel_iff. intros j L w' W K0 K HK s0 s HS.
 assert (Hv : forall r, KB.sval r e = Some v) by (intros r; destruct e; cbn in Hl |- *; try discriminate; exact Hl).
 destruct j as [|j]; [apply KB.ObsT_0|]. apply KB.ObsT_running.
 - destruct e; cbn in Hl; try discriminate; reflexivity.
 - unfold KB.nonterm. rewrite (KB.sval_next sealed rho e v K s (Hv rho)). exact I.
 - intros x. cbn [kont mem]. apply (KB.KRel_throw sealed D); [eapply KB.KRel_down; [|exact HK]; lia|eapply KB.SRel_down; [|exact HS]; lia].
 - intros c1 E1. rewrite (KB.sval_next sealed rho e v K s (Hv rho)) in E1. injection E1 as <-.
   exists (Cfg (Ret v) K0 s0). split; [eapply KB.srun_tau; [apply (KB.sval_next sealed rho0 e v K0 s0 (Hv rho0))|apply KB.srun_refl]|].
   apply (KB.KRel_ret sealed D); [eapply KB.KRel_down; [|exact HK]; lia|exact (lit_vrel e v j w' Hl)|eapply KB.SRel_down; [|exact HS]; lia].
 - intros q kk r E1. rewrite (KB.sval_next sealed rho e v K s (Hv rho)) in E1. discriminate.
Qed.
End Lit.

(* ---------- HT is necessary: share_rule_sound fails for a D without thaw ----------
   Take D = D_hp (hd and tl as the primitives, no thaw: HP holds, and D_wf when hd and tl are
   sealed) and a store holding exactly D_hp, which meets it. The pair
       (if false 0 1)   against   (let G (freeze 1) (if false 0 (thaw G)))
   is accepted by share_rule with rec = cx_rec, syntactic equality of literals, sound at every D by
   lit_kref (proved above, no FrontHyps). The source returns 1. The target, in 9 steps, reaches
   (thaw G), finds no function thaw in the store and raises (XUndefinedFun thaw); every throw the
   source can reach is a resource error (XUser "out of memory" / "stack overflow"). KRef demands
   the source match the target's throw, so the pair is not in KRef and share_rule is not
   rule_sound for this D: share_rule_needs_thaw, with no premise. share_needs_thaw_outright (below)
   adds that D_wf, FrontHyps and HP hold there: of share_rule_sound's premises, HT cannot go. *)
Definition cx_G : name := of_string "G".
Definition cx_src : expr := EIf (EBool false) (ENum (NInt 0)) (ENum (NInt 1)).
Definition cx_tgt : expr := ELet cx_G (EFreeze (ENum (NInt 1))) (EIf (EBool false) (ENum (NInt 0)) (thaw_e cx_G)).
Definition cx_rec (g : list name) (a b : expr) : bool :=
 expr_eqb a b && match lit_val b with Some _ => true | None => false end.
Definition cx_s : store := Store [] [] D_hp.
Definition cx_kif : frame := KIf (ENum (NInt 0)) (ENum (NInt 1)) [].
Definition cx_det : list config :=
 [Cfg (Eval [] cx_src) [] cx_s; Cfg (Eval [] (EBool false)) [cx_kif] cx_s;
  Cfg (Ret (VBool false)) [cx_kif] cx_s; Cfg (Eval [] (ENum (NInt 1))) [] cx_s;
  Cfg (Ret (VNum (NInt 1))) [] cx_s].

Theorem cx_accepted : share_rule cx_rec [] cx_src cx_tgt = true.
Proof. vm_compute. reflexivity. Qed.

Section Cx.
Variable sealed : list name.
Notation R := (jit_rules sealed).
Notation P := jit_profile.

(* Every configuration the source can reach: its own deterministic run, or a resource throw on
   the way out. *)
Definition cx_inv (c : config) : Prop :=
 In c cx_det \/ exists x, (exists r, resource_exn R r = Some x) /\
   In c [Cfg (Throw x) [cx_kif] cx_s; Cfg (Throw x) [] cx_s].

Lemma cx_inv_step : forall c l c1, step_r R P c l c1 -> cx_inv c -> cx_inv c1.
Proof.
 intros c l c1 St [I|(x & Rx & I)].
 - cbn in I. repeat destruct I as [<-|I]; try contradiction; inversion St; subst;
   repeat match goal with E : next_r _ _ _ = _ |- _ => cbn in E end; try discriminate;
   try match goal with E : MTau _ = MTau _ |- _ => injection E as <-; left; cbn; tauto end;
   match goal with Rx : resource_exn _ ?r = Some ?y |- _ =>
     right; exists y; split; [exists r; exact Rx|cbn; tauto] end.
 - cbn in I. repeat destruct I as [<-|I]; try contradiction; inversion St; subst;
   repeat match goal with E : next_r _ _ _ = _ |- _ => cbn in E end;
   repeat match goal with E : running_state _ = _ |- _ => cbn in E end; try discriminate.
   match goal with E : MTau _ = MTau _ |- _ => injection E as <- end.
   right. exists x. split; [exact Rx|cbn; tauto].
Qed.

Lemma cx_inv_star : forall c t c', star (step_r R P) c t c' -> cx_inv c -> cx_inv c'.
Proof. intros c t c' H. induction H as [|c l c1 t c2 St _ IH]; intros I; [exact I|apply IH; exact (cx_inv_step _ _ _ St I)]. Qed.

Lemma cx_runs_tau : forall n c c1 c2, next_r R P c = MTau c1 ->
 JitKRef.JitKRef.runs sealed n c1 [] c2 -> JitKRef.JitKRef.runs sealed (S n) c [] c2.
Proof. intros n c c1 c2 E H. exact (JitKRef.JitKRef.runs_S sealed n c Tau c1 [] c2 (step_r_tau R P c c1 E) H). Qed.

Lemma cx_tgt_runs : JitKRef.JitKRef.runs sealed 9 (Cfg (Eval [] cx_tgt) [] cx_s) []
 (Cfg (Throw (XUndefinedFun thaw_name)) [] (Store [[]] [] D_hp)).
Proof. do 9 (eapply cx_runs_tau; [reflexivity|]). constructor. Qed.

Theorem share_rule_needs_thaw : ~ JitFrontCheck.rule_sound sealed D_hp share_rule.
Proof.
 intros H.
 assert (Hs : JitFrontCheck.chk_sound sealed D_hp cx_rec).
 { intros g a b E. apply andb_true_iff in E as [E1 E2]. apply expr_eqb_eq in E1. subst b.
   destruct (lit_val a) as [v|] eqn:Hl; [|discriminate]. exact (lit_kref sealed D_hp g a v Hl). }
 assert (W0 : wf_world []) by (split; constructor).
 pose proof (H cx_rec Hs [] cx_src cx_tgt cx_accepted 20%nat [] [] [] W0 (fun x I => match I with end)) as K.
 assert (HK : JitKRef.JitKRef.KRel sealed D_hp 20 [] [] []) by exact (JitKRefGround.JitKRefGround.KRel_top sealed D_hp 20 [] W0).
 assert (HS : JitKRef.JitKRef.SRel sealed D_hp 20 [] cx_s cx_s).
 { assert (SH : JitKRef.JitKRef.StoreHas D_hp cx_s) by (intros f d [E|[E|[]]]; injection E as <- <-; reflexivity).
   unfold JitKRef.JitKRef.SRel, JitKRef.JitKRef.SRel_with.
   split; [exact W0|split; [exact SH|split; [exact SH|split; [reflexivity|split; [constructor|]]]]].
   intros l0 l []. }
 pose proof (K 20%nat (le_n _) [] (JitKRefGround.JitKRefGround.wext_refl [] W0) [] [] HK cx_s cx_s HS) as O.
 destruct (O 9%nat [] _ ltac:(lia) cx_tgt_runs) as (_ & B & _).
 destruct (B _ _ eq_refl) as (s0 & w' & S0 & _).
 destruct (cx_inv_star _ _ _ S0 (or_introl (or_introl eq_refl))) as [I|(x & (r & Rx) & I)].
 - cbn in I. repeat destruct I as [E|I]; try discriminate; contradiction.
 - cbn in I. repeat destruct I as [E|I]; try discriminate; try contradiction.
   injection E as -> _. destruct r; discriminate.
Qed.

(* The form of share_rule_sound without HT, at D_hp, would refute FrontHyps there. *)
Corollary share_rule_sound_needs_thaw :
 (JitFrontCheck.FrontHyps sealed D_hp -> JitFrontCheck.rule_sound sealed D_hp share_rule) ->
 ~ JitFrontCheck.FrontHyps sealed D_hp.
Proof. intros H FH. exact (share_rule_needs_thaw (H FH)). Qed.
End Cx.

(* With KRef's fundamental property proved, FrontHyps holds at D_hp whenever hd and tl are sealed
   (D_wf), and HP holds there, so the counterexample above is unconditional: D_wf, FrontHyps and HP
   hold at D_hp, and share_rule is still not rule_sound. Of share_rule_sound's premises (HT, HP,
   D_wf), HT cannot be dropped. *)
Lemma hd_tl_differ : hd_name <> tl_name.
Proof. intro E. vm_compute in E. discriminate E. Qed.

Theorem share_needs_thaw_outright : forall sealed, In hd_name sealed -> In tl_name sealed ->
 JitKRef.JitKRef.D_wf sealed D_hp /\ FrontHyps sealed D_hp /\
 (In (hd_name, FPrim PHd) D_hp /\ In (tl_name, FPrim PTl) D_hp) /\
 ~ JitFrontCheck.rule_sound sealed D_hp share_rule.
Proof.
 intros sealed Ih It.
 assert (Dw : JitKRef.JitKRef.D_wf sealed D_hp).
 { split; [repeat constructor; assumption|]. constructor; [|constructor; [intros []|constructor]].
   intros [E|[]]. exact (hd_tl_differ (eq_sym E)). }
 split; [exact Dw|split; [apply front_hyps; exact Dw|split; [split; [left; reflexivity|right; left; reflexivity]|]]].
 exact (share_rule_needs_thaw sealed).
Qed.

(* ---------- HT for the real D: where thaw's entry comes from, and what blocks it ----------
   (a) Under jit_rules no step adds, removes or changes the function of a fixed name, thaw among
       them (is_fixed_name: defun refuses it, kernel's own (defun thaw (V3830) (V3830)) included,
       thaw_defun_refused). So lookup thaw in a store is fixed for the whole run (thaw_stable): a D
       holding thaw describes the store before the first step, the image's initial store, which no
       stage 0 code can establish in this model. Relating that store to the image is OB-JIT-IMAGE.
   (b) Comp has no rule for a dynamic application (comp_no_app): no code object is related to
       thaw's body (EApp (EVar V) []), so a store holding the kernel's thaw has no machine with
       Com s m (ht_not_com), and D_compiled is false for every code list (ht_not_compiled).
       call_preservation_src takes StoreHas s and Com s m, so with HT its premises cannot all hold
       until an emission family relates the 0-ary dynamic apply (the binary's tail-call-value).
   (c) HT is consistent with D_wf (ht_dwf_sat, HT alone); HT, HP and D_wf hold together at D_share
       (share_premises_sat, below), so check_share_sound is not vacuous. *)
Definition kernel_thaw (tp : name) : fundef := FUser [tp] (EApp (EVar tp) []).

Theorem thaw_fixed : is_fixed_name thaw_name = true.
Proof. vm_compute. reflexivity. Qed.

Theorem thaw_defun_refused : forall sealed rho ps b k s,
 eval_move_r (jit_rules sealed) jit_profile rho (EDefun thaw_name ps b) k s = MTau (Cfg (Throw XBadDefinition) k s).
Proof.
 intros sealed rho ps b k s. apply defun_refused. cbn [defun_allowed jit_rules]. rewrite thaw_fixed. reflexivity.
Qed.

Theorem fixed_step : forall sealed c l c' f, step_r (jit_rules sealed) jit_profile c l c' -> is_fixed_name f = true ->
 lookup f (gfuns (mem c')) = lookup f (gfuns (mem c)).
Proof.
 intros sealed c l c' f H I. destruct (KB.step_gfd sealed _ _ _ H) as [E|(g & d & Da & E)]; rewrite E; [reflexivity|].
 cbn [lookup]. destruct (text_eqb f g) eqn:T; [|reflexivity]. exfalso. apply text_eqb_eq in T. subst g.
 change (negb (is_fixed_name f || existsb (text_eqb f) sealed) = true) in Da. rewrite I in Da. discriminate.
Qed.

Theorem thaw_stable : forall sealed c t c', JitKRef.JitKRef.srun sealed c t c' ->
 lookup thaw_name (gfuns (mem c')) = lookup thaw_name (gfuns (mem c)).
Proof.
 intros sealed c t c' H. unfold JitKRef.JitKRef.srun in H.
 induction H as [c|c l c1 t c2 St H IH]; [reflexivity|]. rewrite IH. exact (fixed_step sealed _ _ _ _ St thaw_fixed).
Qed.

Lemma comp_no_app_slot : forall c g top h l d r r', ~ Comp c g top (EApp h l) (DSlot d) r r'.
Proof. intros c g top h l d r r' H. inversion H; subst; cbn in *; discriminate. Qed.

Theorem comp_no_app : forall c g top h l dst r r', ~ Comp c g top (EApp h l) dst r r'.
Proof.
 intros c g top h l [d|] r r' H; [exact (comp_no_app_slot c g top h l d r r' H)|].
 inversion H; subst; cbn in *; try discriminate.
 match goal with Ho : CompOp _ _ _ (EApp _ _) _ _ _ _ |- _ => inversion Ho; subst; cbn in *; try discriminate end.
 match goal with Hc : Comp _ _ _ (EApp _ _) (DSlot _) _ _ |- _ => exact (comp_no_app_slot _ _ _ _ _ _ _ _ Hc) end.
Qed.

Theorem ht_not_com : forall D tp s m, In (thaw_name, kernel_thaw tp) D ->
 JitKRef.JitKRef.StoreHas D s -> ~ JitLowerStep.JitLowerStep.Com s m.
Proof.
 intros D tp s m I SH [_ F]. destruct (JitLowerStep.JitLowerStep.fr_user s m F thaw_name [tp] (EApp (EVar tp) []) (SH _ _ I))
   as (l & c & caps & _ & _ & _ & _ & r' & Hc).
 exact (comp_no_app _ _ _ _ _ _ _ _ Hc).
Qed.

Theorem ht_not_compiled : forall D tp cs, In (thaw_name, kernel_thaw tp) D -> JitKRef.JitKRef.D_compiled D cs = false.
Proof.
 intros D tp cs I. apply Bool.not_true_iff_false. intro H. unfold JitKRef.JitKRef.D_compiled in H.
 rewrite forallb_forall in H. specialize (H _ I). cbn [fst snd kernel_thaw] in H.
 destruct (lookup thaw_name cs) as [c|]; [|discriminate].
 apply JitLowerCheck.JitLowerCheck.check_fn_sound in H. destruct H as (r' & Hc). exact (comp_no_app _ _ _ _ _ _ _ _ Hc).
Qed.

Theorem ht_dwf_sat : forall tp, JitKRef.JitKRef.D_wf [thaw_name] [(thaw_name, kernel_thaw tp)] /\
 In (thaw_name, kernel_thaw tp) [(thaw_name, kernel_thaw tp)].
Proof.
 intros tp. split; [split|left; reflexivity].
 - constructor; [left; reflexivity|constructor].
 - constructor; [intros []|constructor].
Qed.

(* ---------- HP is necessary: share's reuse fails for a D that leaves hd or tl open ----------
   Take o in {hd, tl} and D = [thaw as the kernel's; the other of hd/tl as its primitive], sealed
   = [thaw; hd; tl]: D_wf, FrontHyps and HT hold, and HP fails on o's half only. KRef ranges over
   every store meeting D, and a store may hold o as a user function with an effect: here o returns
   the counter hx-counter's old value and sets it to 1. The pair (rec: scoped syntactic equality,
   sound by KRef_refl)
       (if (let S (o V) true) (o V) 0)   against   (let G (freeze 0) (let S (o V) (if true S (thaw G))))
   is share_rule's reuse of S for (o V) (hx_accepted). From the counter at 0 the target calls o once
   and returns 0 (hx_tgt_runs, 25 steps); every run of the source is on its deterministic path,
   which calls o twice and returns 1 and nothing else, or a throw under frames without a trap
   (hx_inv_star, over the path reach computes). KRef demands a source value equal to the target's
   0, so share_rule is not rule_sound at that D: share_needs_hd_tl. Of share_rule_sound's
   premises, neither half of HP can be dropped. *)
Definition share_sealed : list name := [thaw_name; hd_name; tl_name].
Definition hx_V : name := of_string "V".
Definition hx_S : name := of_string "S".
Definition hx_G : name := of_string "G".
Definition hx_O : name := of_string "Old".
Definition hx_Z : name := of_string "Z".
Definition hx_c : name := of_string "hx-counter".
Definition hx_tp : name := of_string "X".
Definition hx_op (o : bool) : name := if o then hd_name else tl_name.
Definition hx_prim (o : bool) : prim := if o then PHd else PTl.
Definition hx_D (o : bool) : list (name * fundef) :=
 [(thaw_name, kernel_thaw hx_tp); (hx_op (negb o), FPrim (hx_prim (negb o)))].
Definition hx_src (o : bool) : expr :=
 EIf (ELet hx_S (ECall (hx_op o) [EVar hx_V]) (EBool true)) (ECall (hx_op o) [EVar hx_V]) (ENum (NInt 0)).
Definition hx_tgt (o : bool) : expr :=
 ELet hx_G (EFreeze (ENum (NInt 0))) (ELet hx_S (ECall (hx_op o) [EVar hx_V]) (EIf (EBool true) (EVar hx_S) (thaw_e hx_G))).
Definition hx_rec (g : list name) (a b : expr) : bool := expr_eqb a b && JitKRef.JitKRef.scoped g a.
Definition hx_body : expr := ELet hx_O (ECall (of_string "value") [ESym hx_c])
  (ELet hx_Z (ECall (of_string "set") [ESym hx_c; ENum (NInt 1)]) (EVar hx_O)).
Definition hx_s (o : bool) : store := Store [] [(hx_c, VNum (NInt 0))]
  ((thaw_name, kernel_thaw hx_tp) :: (hx_op (negb o), FPrim (hx_prim (negb o))) :: (hx_op o, FUser [hx_tp] hx_body) ::
   (of_string "value", FPrim PValue) :: (of_string "set", FPrim PSet) :: []).
Definition hx_rho : lenv := [(hx_V, VNil)].

Theorem hx_accepted : forall o, share_rule hx_rec [hx_V] (hx_src o) (hx_tgt o) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Hx.
Notation R := (jit_rules share_sealed).
Notation P := jit_profile.

Fixpoint reach (n : nat) (c : config) : option (list config) := match n with
 | 0 => None
 | S n => match next_r R P c with MTau c1 => option_map (cons c) (reach n c1) | _ => Some [c] end end.

Lemma reach_head : forall n c l, reach n c = Some l -> In c l.
Proof.
 intros [|n] c l H; cbn in H; [discriminate|]. destruct (next_r R P c); try (injection H as <-; left; reflexivity).
 destruct (reach n c0); cbn in H; [injection H as <-; left; reflexivity|discriminate].
Qed.

Lemma reach_closed : forall n c l, reach n c = Some l -> forall x x1, In x l -> next_r R P x = MTau x1 -> In x1 l.
Proof.
 induction n as [|n IH]; intros c l H x x1 I E; cbn in H; [discriminate|].
 destruct (next_r R P c) eqn:Ec; try (injection H as <-; destruct I as [<-|[]]; rewrite Ec in E; discriminate).
 destruct (reach n c0) as [l'|] eqn:El; cbn in H; [|discriminate]. injection H as <-.
 destruct I as [<-|I].
 - rewrite Ec in E. injection E as <-. right. exact (reach_head n _ _ El).
 - right. exact (IH _ _ El x x1 I E).
Qed.

Definition hx_inv (l : list config) (c : config) : Prop :=
 In c l \/ exists x K s, c = Cfg (Throw x) K s /\ forallb KB.nontrap K = true.

Lemma hx_inv_step : forall n c0 l, reach n c0 = Some l ->
 forallb (fun c => match next_r R P c with MIO _ _ => false | _ => true end) l = true ->
 forallb (fun c => forallb KB.nontrap (kont c)) l = true ->
 forall c lb c1, step_r R P c lb c1 -> hx_inv l c -> hx_inv l c1.
Proof.
 intros n c0 l Hl Hio Hnt c lb c1 St [I|(x & K & s & -> & Hk)].
 - inversion St as [c' c'' E|c' q kk r E|c' r x Rs Rx]; subst.
   + left. exact (reach_closed n c0 l Hl c c1 I E).
   + rewrite forallb_forall in Hio. specialize (Hio c I). rewrite E in Hio. discriminate.
   + right. exists x, (kont c), (mem c). split; [reflexivity|]. rewrite forallb_forall in Hnt. exact (Hnt c I).
 - right. destruct K as [|f K].
   + inversion St as [c' c'' E|c' q kk r E|c' r y Rs Rx]; subst; cbn in *; discriminate.
   + cbn in Hk. apply andb_true_iff in Hk as [Hf Hk]. pose proof (KB.throw_frame_next share_sealed f x K s Hf) as T.
     inversion St as [c' c'' E|c' q kk r E|c' r y Rs Rx]; subst; [|rewrite T in E; discriminate|cbn in Rs; discriminate].
     rewrite T in E. injection E as <-. exists x, K, s. split; [reflexivity|exact Hk].
Qed.

Lemma hx_inv_star : forall n c0 l, reach n c0 = Some l ->
 forallb (fun c => match next_r R P c with MIO _ _ => false | _ => true end) l = true ->
 forallb (fun c => forallb KB.nontrap (kont c)) l = true ->
 forall c t c', star (step_r R P) c t c' -> hx_inv l c -> hx_inv l c'.
Proof.
 intros n c0 l Hl Hio Hnt c t c' H. induction H as [|c lb c1 t c2 St _ IH]; intros I; [exact I|].
 apply IH. exact (hx_inv_step n c0 l Hl Hio Hnt _ _ _ St I).
Qed.

Definition ret_one (c : config) : bool := match ctl c, kont c with
 | Ret (VNum (NInt 1)), [] => true | Ret _, [] => false | _, _ => true end.

Lemma hx_src_reach : forall o, exists l, reach 60 (Cfg (Eval hx_rho (hx_src o)) [] (hx_s o)) = Some l /\
 forallb (fun c => match next_r R P c with MIO _ _ => false | _ => true end) l = true /\
 forallb (fun c => forallb KB.nontrap (kont c)) l = true /\ forallb ret_one l = true.
Proof. intros [|]; (eexists; split; [vm_compute; reflexivity|vm_compute; repeat split]). Qed.

Lemma hx_tgt_runs : forall o, exists s', JitKRef.JitKRef.runs share_sealed 25 (Cfg (Eval hx_rho (hx_tgt o)) [] (hx_s o)) []
 (Cfg (Ret (VNum (NInt 0))) [] s').
Proof. intros [|]; eexists; do 25 (eapply cx_runs_tau; [vm_compute; reflexivity|]); constructor. Qed.

Lemma thaw_hd_differ : thaw_name <> hd_name.
Proof. intro E. vm_compute in E. discriminate E. Qed.
Lemma thaw_tl_differ : thaw_name <> tl_name.
Proof. intro E. vm_compute in E. discriminate E. Qed.

Theorem share_needs_hd_tl : forall o,
 JitKRef.JitKRef.D_wf share_sealed (hx_D o) /\ FrontHyps share_sealed (hx_D o) /\
 In (thaw_name, kernel_thaw hx_tp) (hx_D o) /\
 In (hx_op (negb o), FPrim (hx_prim (negb o))) (hx_D o) /\ ~ In (hx_op o, FPrim (hx_prim o)) (hx_D o) /\
 ~ JitFrontCheck.rule_sound share_sealed (hx_D o) share_rule.
Proof.
 intros o.
 assert (Dw : JitKRef.JitKRef.D_wf share_sealed (hx_D o)).
 { split.
   - destruct o; (constructor; [cbn; tauto|constructor; [cbn; tauto|constructor]]).
   - constructor; [|constructor; [intros []|constructor]].
     intros [E|[]]. destruct o; cbn in E; [exact (thaw_tl_differ (eq_sym E))|exact (thaw_hd_differ (eq_sym E))]. }
 split; [exact Dw|split; [apply front_hyps; exact Dw|split; [left; reflexivity|split; [right; left; reflexivity|split]]]].
 { intros [E|[E|[]]]; injection E; destruct o; discriminate. }
 intros H.
 assert (Hs : JitFrontCheck.chk_sound share_sealed (hx_D o) hx_rec).
 { intros g a b E. apply andb_true_iff in E as [E1 E2]. apply expr_eqb_eq in E1. subst b.
   exact (JitKRefFund.JitKRefFund.KRef_refl share_sealed (hx_D o) g a Dw E2). }
 assert (W0 : JitKRef.JitKRef.wf_world []) by (split; constructor).
 assert (HE : JitKRef.JitKRef.EnvRel_with (JitKRef.JitKRef.VRel share_sealed (hx_D o) 40) [] [hx_V] hx_rho hx_rho).
 { intros x [<-|[]]. exists VNil, VNil. split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|]].
   exact (lit_vrel share_sealed (hx_D o) ENil VNil 40 [] eq_refl). }
 pose proof (H hx_rec Hs [hx_V] (hx_src o) (hx_tgt o) (hx_accepted o) 40%nat [] hx_rho hx_rho W0 HE) as K.
 assert (HK : JitKRef.JitKRef.KRel share_sealed (hx_D o) 40 [] [] []) by exact (JitKRefGround.JitKRefGround.KRel_top share_sealed (hx_D o) 40 [] W0).
 assert (HS : JitKRef.JitKRef.SRel share_sealed (hx_D o) 40 [] (hx_s o) (hx_s o)).
 { assert (SH : JitKRef.JitKRef.StoreHas (hx_D o) (hx_s o)) by (intros f d [E|[E|[]]]; injection E as <- <-; destruct o; vm_compute; reflexivity).
   unfold JitKRef.JitKRef.SRel, JitKRef.JitKRef.SRel_with.
   split; [exact W0|split; [exact SH|split; [exact SH|split; [reflexivity|split]]]].
   - constructor; [split; [reflexivity|cbn [snd]; exact (lit_vrel share_sealed (hx_D o) (ENum (NInt 0)) (VNum (NInt 0)) 40 [] eq_refl)]|constructor].
   - intros l0 l []. }
 pose proof (proj1 (KB.ERel_iff share_sealed (hx_D o) _ _ _ _ _ _) K 40%nat (le_n _) [] (JitKRefGround.JitKRefGround.wext_refl [] W0) [] [] HK (hx_s o) (hx_s o) HS) as O.
 destruct (hx_tgt_runs o) as (s' & Rt).
 destruct (O 25%nat [] _ ltac:(lia) Rt) as (B & _).
 destruct (B _ _ eq_refl) as (v0 & s0 & w' & S0 & _ & G & _).
 destruct (hx_src_reach o) as (l & Hl & Hio & Hnt & H1).
 destruct (hx_inv_star 60 _ l Hl Hio Hnt _ _ _ S0 (or_introl (reach_head 60 _ _ Hl))) as [I|(x & K' & s1 & E & _)]; [|discriminate E].
 rewrite forallb_forall in H1. specialize (H1 _ I). unfold ret_one in H1. cbn in H1.
 destruct v0 as [n| | | | | | | | | | |]; try discriminate; destruct n as [z|]; try discriminate.
 cbn in G. destruct z as [|[| |]|]; try discriminate.
Qed.
End Hx.

(* The premises of check_share_sound hold together: D_share (thaw as the kernel's, hd and tl as the
   primitives, the three sealed) meets D_wf, HT and HP. So check_share_sound is not vacuous. This
   says nothing of the pinned build's D or sealed: relating them to the image is OB-JIT-IMAGE and
   OB-JIT-IMAGE-SEALING, and with HT no store has Com (ht_not_com). *)
Definition D_share (tp : name) : list (name * fundef) :=
 [(thaw_name, kernel_thaw tp); (hd_name, FPrim PHd); (tl_name, FPrim PTl)].

Theorem share_premises_sat : forall tp, JitKRef.JitKRef.D_wf share_sealed (D_share tp) /\
 In (thaw_name, FUser [tp] (EApp (EVar tp) [])) (D_share tp) /\
 (In (hd_name, FPrim PHd) (D_share tp) /\ In (tl_name, FPrim PTl) (D_share tp)).
Proof.
 intros tp. split; [split|split; [left; reflexivity|split; [right; left; reflexivity|right; right; left; reflexivity]]].
 - constructor; [left; reflexivity|constructor; [right; left; reflexivity|constructor; [right; right; left; reflexivity|constructor]]].
 - constructor; [|constructor; [|constructor; [intros []|constructor]]].
   + intros [E|[E|[]]]; cbn in E; [exact (thaw_hd_differ (eq_sym E))|exact (thaw_tl_differ (eq_sym E))].
   + intros [E|[]]. cbn in E. exact (hd_tl_differ (eq_sym E)).
Qed.

(* fresh_ok's premise gives the checker's freshness tests for the lowerer's own names: a name the
   source never mentions is in no scope built from the source's binders and parameters. *)
Theorem fresh_not_bound : forall ns g G, (forall x, In x g -> reserved ns x = false) -> reserved ns G = true ->
 bound g G = false.
Proof.
 intros ns g G H RG. unfold bound. apply Bool.not_true_iff_false. intro B.
 apply existsb_exists in B as (y & I & T). apply text_eqb_eq in T. subst y.
 rewrite (H G I) in RG. discriminate.
Qed.
End JitFrontShare.
