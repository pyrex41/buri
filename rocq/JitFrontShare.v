(* Shen/JIT Phase 2, F00: the share pass's checker, an instance of JitFrontCheck.fchk.
   lower.shen (934cfa5) `share` rewrites (if C X Y), where C is a chain of `and` tests and `let`
   bindings, to
       (let ElseN (freeze Y') (unchain C X' ElseN))
   where (unchain (and T S) Then G) = (if T (unchain S Then G) (thaw G)),
         (unchain (let V E S) Then G) = (let V E (unchain S Then G)),
         (unchain T Then G)           = (if T Then (thaw G)),
   and recurses into let bodies, do's second argument and if branches (the same-head case of fchk).

   share_rule accepts (if C X Y) against (let G (freeze Y') U) when
   - G is not in the scope g and id_key is not in g (the target-only bindings G and the frozen
     closure's identity tag shadow nothing the source reads);
   - rec g Y Y';
   - chain_chk: U is C unchained, each test checked by rec in the chain's scope, each chain
     binder V outside g and different from G, every else branch exactly (thaw G) for this G, and
     the then branch checked by rec g X X' in the OUTER scope g.
   share_rule_sound: the target's let, freeze and the push of the frozen closure take three target
   steps; the frozen closure's cell is target-only and lies outside the world (SRel_with_cell_tgt);
   each (thaw G) takes six target steps to reach Y' in the closure's environment, paid from the
   index (thaw_erel); the source's and/KAndR/if frames are related to the target's if frames
   frame by frame (kif_base, kand_frame), and a chain let binds the same name on both sides
   (chain_sound). The thaw steps go through the store's thaw, so the soundness takes, as a
   premise, that D defines thaw as the kernel does: (defun thaw (V) (V)) (Section hypothesis HT).
   HT is necessary: share_rule_needs_thaw (below) proves that KRef_refl at D = [] refutes
   share_rule_sound there, so the FrontHyps-only form the spec asked for holds only if FrontHyps
   fails at D = [] (share_rule_sound_needs_thaw), which kref-fund is to prove false.

   NOT covered: share's REUSE of a chain-bound variable for a hd/tl the chain already took (the
   `reuse` / `canon` part of lower.shen's share, "share chains"). Relating (hd V) on the source to
   a variable bound to its value on the target needs an environment invariant KRef does not carry.
   Every share rewrite of stage 0 reuses, so check_share rejects those definitions, each named with
   a Rocq rejection trace (share_trace).

   Freshness: the checker tests the freshness facts it needs (G and the chain binders outside the
   scope, and from each other) directly; fresh_not_bound shows that fresh_ok's reserved-name
   premise implies them for the lowerer's names. no_keyword_binders is not used here: the checker
   reads Rocq's parse, where (thaw G) is a named call whatever binds what; it matters for parse
   fidelity (the binary reading the forms as Rocq does), which is call_preservation_src's premise. *)
From Coq Require Import List ZArith NArith PArith Bool String Ascii Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitFrontCheck JitLowerStage0.
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

(* U is the chain C unchained with then branch X (checked against the target's in scope g0) and
   else label G; g is the chain's scope so far (g0 plus the chain binders). *)
Definition base_chk (rec : list name -> expr -> expr -> bool) (g0 : list name) (G : name) (X : expr)
  (g : list name) (C U : expr) : bool :=
 match U with
 | EIf T' X' Z => is_thaw_of G Z && rec g C T' && rec g0 X X'
 | _ => false end.

Fixpoint chain_chk (rec : list name -> expr -> expr -> bool) (g0 : list name) (G : name) (X : expr)
  (g : list name) (C U : expr) {struct C} : bool :=
 base_chk rec g0 G X g C U
 || match C, U with
 | EAnd T Sc, EIf T' U1 Z => is_thaw_of G Z && rec g T T' && chain_chk rec g0 G X g Sc U1
 | ELet x E Sc, ELet x' E' U1 => text_eqb x x' && negb (bound g0 x) && negb (text_eqb x G) &&
     rec g E E' && chain_chk rec g0 G X (x :: g) Sc U1
 | _, _ => false end.

Definition share_rule : rule := fun rec g e0 e => match e0, e with
 | EIf C X Y, ELet G (EFreeze Y') U =>
   negb (bound g G) && negb (bound g id_key) && rec g Y Y' && chain_chk rec g G X g C U
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
Fixpoint chain_why (rec : list name -> expr -> expr -> bool) (g0 : list name) (G : name) (X : expr)
  (g : list name) (C U : expr) {struct C} : string :=
 let base := match U with
   | EIf T' X' Z =>
     if negb (is_thaw_of G Z) then "share: an else branch is not (thaw ElseN)"
     else if negb (rec g C T') then "share: a chain test differs"
     else if negb (rec g0 X X') then "share: the then branch differs from the source's (share's reuse of a chain variable is not covered)"
     else "share: base accepted"
   | _ => "share: not an unchained if" end in
 match C, U with
 | EAnd T Sc, EIf T' U1 Z =>
   if is_thaw_of G Z && rec g T T' then chain_why rec g0 G X g Sc U1 else base
 | ELet x E Sc, ELet x' E' U1 =>
   if text_eqb x x' && negb (bound g0 x) && negb (text_eqb x G) && rec g E E'
   then chain_why rec g0 G X (x :: g) Sc U1 else "share: a chain let differs, or binds a name of the scope or ElseN"
 | _, _ => base end.

Definition share_why (rec : list name -> expr -> expr -> bool) (g : list name) (e0 e : expr) : list string :=
 match e0, e with
 | EIf C X Y, ELet G (EFreeze Y') U =>
   [if bound g G then "share: ElseN is in scope"
    else if bound g id_key then "share: the identity key is in scope"
    else if negb (rec g Y Y') then "share: the frozen else differs from the source's"
    else chain_why rec g G X g C U]
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
Local Close Scope string_scope.

(* ---------- soundness ---------- *)
Definition andRs (m : nat) : list frame := repeat KAndR m.

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
Definition CRel (k : nat) (w : world) (X Y : expr) (rho0 rho0i : lenv) (C : expr) (rhoi : lenv) (U : expr)
  (m : nat) : Prop :=
 forall j w' K0 K s0 s, (j <= k)%nat -> wext w w' -> KRel j w' K0 K -> SRel j w' s0 s ->
  ObsT j w' (Cfg (Eval rho0i C) (andRs m ++ KIf X Y rho0 :: K0) s0) (Cfg (Eval rhoi U) K s).

Section Chain.
Variable rec : list name -> expr -> expr -> bool.
Hypothesis Hr : chk_sound rec.
Variables (g0 : list name) (G : name) (X Y Y' : expr) (rT rho0 : lenv).

Definition chain_hyps (k : nat) (w : world) (g : list name) (rho0i rhoi : lenv) : Prop :=
 wf_world w /\ EnvRel_with (VRel k) w g rho0i rhoi /\ EnvRel_with (VRel k) w g0 rho0 rhoi /\
 lookup G rhoi = Some (VFrozen Y' rT) /\ ERel k w rho0 Y rT Y'.

Lemma chain_hyps_mono : forall k j w w' g r0 r, (j <= k)%nat -> wext w w' -> chain_hyps k w g r0 r -> chain_hyps j w' g r0 r.
Proof.
 intros k j w w' g r0 r L W (Wf & H1 & H2 & H3 & H4). split; [exact (proj2 W)|].
 split; [eapply KB.EnvRel_mono; eauto|split; [eapply KB.EnvRel_mono; eauto|split; [exact H3|eapply KB.ERel_mono; eauto]]].
Qed.

Lemma thaw_from_hyps : forall k w g r0 r, chain_hyps k w g r0 r ->
 forall j w', (j <= k)%nat -> wext w w' -> ERel j w' rho0 Y r (thaw_e G).
Proof.
 intros k w g r0 r (Wf & H1 & H2 & H3 & H4) j w' L W. eapply thaw_erel; [exact H3|]. eapply KB.ERel_mono; eauto.
Qed.

Lemma then_from_hyps : forall k w g r0 r X', rec g0 X X' = true -> chain_hyps k w g r0 r ->
 forall j w', (j <= k)%nat -> wext w w' -> ERel j w' rho0 X r X'.
Proof.
 intros k w g r0 r X' E (Wf & H1 & H2 & H3 & H4) j w' L W. apply (Hr g0 X X' E); [exact (proj2 W)|].
 eapply KB.EnvRel_mono; eauto.
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

Lemma chain_base : forall k w m g rho0i rhoi C U, chain_hyps k w g rho0i rhoi ->
 base_chk rec g0 G X g C U = true -> CRel k w X Y rho0 rho0i C rhoi U m.
Proof.
 intros k w m g rho0i rhoi C U Hh E. unfold base_chk in E. destruct U as [| | | | | | | | U1 U2 U3 | | | | | | | | |]; try discriminate.
 apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2]. apply is_thaw_of_eq in E1. subst U3.
 intros j w' K0 K s0 s L W HK HS. destruct j as [|j]; [apply KB.ObsT_0|].
 apply (tgt_tau _ _ _ _ (Cfg (Eval rhoi U1) (KIf U2 (thaw_e G) rhoi :: K) s)); [reflexivity|reflexivity| |].
 - intros x. cbn [kont mem]. rewrite stack_eq.
   apply (throw_pop (S j) w' K0 K (andRs m ++ [KIf X Y rho0]) []); [exact HK|apply nontrap_andRs; reflexivity|reflexivity|lia|eapply KB.wext_self; exact HS|].
   eapply KB.SRel_down; [|exact HS]; lia.
 - assert (Hj : chain_hyps j w' g rho0i rhoi) by (eapply chain_hyps_mono; [|exact W|exact Hh]; lia).
   pose proof Hj as Hjj. destruct Hj as (Wf & HE & HE0 & HG & HY).
   eapply KB.ERel_apply; [apply (Hr g C U1 E2); [exact Wf|exact HE]|apply le_n|eapply KB.wext_self; exact HS| |].
   + apply kif_base; [eapply KB.KRel_down; [|exact HK]; lia| |].
     * intros j' w'' L' W'. eapply then_from_hyps; [exact E3|exact Hjj|exact L'|exact W'].
     * intros j' w'' L' W'. eapply thaw_from_hyps; [exact Hjj|exact L'|exact W'].
   + eapply KB.SRel_down; [|exact HS]; lia.
Qed.

Lemma chain_and : forall k w m g rho0i rhoi T Sc U1 T' Z,
 chain_hyps k w g rho0i rhoi -> is_thaw_of G Z = true -> rec g T T' = true ->
 CRel k w X Y rho0 rho0i Sc rhoi U1 (S m) ->
 CRel k w X Y rho0 rho0i (EAnd T Sc) rhoi (EIf T' U1 Z) m.
Proof.
 intros k w m g rho0i rhoi T Sc U1 T' Z Hh Ez Et IH. apply is_thaw_of_eq in Ez. subst Z.
 intros j w' K0 K s0 s L W HK HS. destruct j as [|j]; [apply KB.ObsT_0|].
 apply KB.ObsT_running; [reflexivity|unfold KB.nonterm; cbn; exact I| | |].
 - intros x. cbn [kont mem]. rewrite stack_eq.
   apply (throw_pop (S j) w' K0 K (andRs m ++ [KIf X Y rho0]) []); [exact HK|apply nontrap_andRs; reflexivity|reflexivity|lia|eapply KB.wext_self; exact HS|].
   eapply KB.SRel_down; [|exact HS]; lia.
 - intros c1 E1. cbn in E1. injection E1 as <-.
   exists (Cfg (Eval rho0i T) (KAnd Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) s0).
   split; [eapply KB.srun_tau; [reflexivity|apply KB.srun_refl]|].
   assert (Hj : chain_hyps j w' g rho0i rhoi) by (eapply chain_hyps_mono; [|exact W|exact Hh]; lia).
   pose proof Hj as Hjj. destruct Hj as (Wf & HE & HE0 & HG & HY).
   eapply KB.ERel_apply; [apply (Hr g T T' Et); [exact Wf|exact HE]|apply le_n|eapply KB.wext_self; exact HS| |].
   + apply kand_frame; [eapply KB.KRel_down; [|exact HK]; lia| |].
     * intros j' w'' L' W'. eapply thaw_from_hyps; [exact Hjj|exact L'|exact W'].
     * intros j' w'' s0' s' L' W' HS'. apply (IH j' w'' K0 K s0' s'); [lia|eapply KB.wext_trans; [exact W|exact W']| |exact HS'].
       eapply KB.KRel_mono; [|exact W'|exact HK]. lia.
   + eapply KB.SRel_down; [|exact HS]; lia.
 - intros q kk r E1. cbn in E1. discriminate.
Qed.

Lemma chain_let : forall k w m g rho0i rhoi x E Sc E' U1,
 chain_hyps k w g rho0i rhoi -> bound g0 x = false -> text_eqb x G = false -> rec g E E' = true ->
 (forall k' w' v0 v, (k' <= k)%nat -> wext w w' -> chain_hyps k' w' (x :: g) ((x, v0) :: rho0i) ((x, v) :: rhoi) ->
    CRel k' w' X Y rho0 ((x, v0) :: rho0i) Sc ((x, v) :: rhoi) U1 m) ->
 CRel k w X Y rho0 rho0i (ELet x E Sc) rhoi (ELet x E' U1) m.
Proof.
 intros k w m g rho0i rhoi x E Sc E' U1 Hh Bx Gx Ee IH.
 intros j w' K0 K s0 s L W HK HS. destruct j as [|j]; [apply KB.ObsT_0|].
 apply KB.ObsT_running; [reflexivity|unfold KB.nonterm; cbn; exact I| | |].
 - intros x'. cbn [kont mem]. rewrite stack_eq.
   apply (throw_pop (S j) w' K0 K (andRs m ++ [KIf X Y rho0]) []); [exact HK|apply nontrap_andRs; reflexivity|reflexivity|lia|eapply KB.wext_self; exact HS|].
   eapply KB.SRel_down; [|exact HS]; lia.
 - intros c1 E1. cbn in E1. injection E1 as <-.
   exists (Cfg (Eval rho0i E) (KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) s0).
   split; [eapply KB.srun_tau; [reflexivity|apply KB.srun_refl]|].
   assert (Hj : chain_hyps j w' g rho0i rhoi) by (eapply chain_hyps_mono; [|exact W|exact Hh]; lia).
   pose proof Hj as Hjj. destruct Hj as (Wf & HE & HE0 & HG & HY).
   eapply KB.ERel_apply; [apply (Hr g E E' Ee); [exact Wf|exact HE]|apply le_n|eapply KB.wext_self; exact HS| |].
   + change (KLet x Sc rho0i :: andRs m ++ KIf X Y rho0 :: K0) with ([KLet x Sc rho0i] ++ andRs m ++ KIf X Y rho0 :: K0).
     rewrite stack_eq, app_assoc.
     apply krel_build; [eapply KB.KRel_down; [|exact HK]; lia|cbn; apply nontrap_andRs; reflexivity|reflexivity| |].
     * intros j' w'' v0 v s0' s' c1 L' W' HV HS' E2. cbn in E2. injection E2 as <-.
       rewrite <- app_assoc, <- stack_eq. cbn [app].
       eexists; split; [eapply KB.srun_tau; [reflexivity|apply KB.srun_refl]|].
       assert (Hx : chain_hyps j' w'' (x :: g) ((x, v0) :: rho0i) ((x, v) :: rhoi)).
       { destruct (chain_hyps_mono j j' w' w'' g rho0i rhoi ltac:(lia) W' Hjj) as (Wf' & HE' & HE0' & HG' & HY').
         split; [exact Wf'|split; [|split; [|split; [|exact HY']]]].
         - apply EnvRel_cons_same; [eapply KB.VRel_down; [|exact HV]; lia|exact HE'].
         - apply EnvRel_cons_r; [apply bound_false; exact Bx|exact HE0'].
         - cbn. rewrite text_eqb_neq in Gx. destruct (text_eqb G x) eqn:T; [|exact HG'].
           apply text_eqb_eq in T. subst. contradiction. }
       pose proof (IH j' w'' v0 v ltac:(lia) (KB.wext_trans _ _ _ W W') Hx) as Hc.
       apply (Hc j' w'' K0 K s0' s'); [apply le_n|eapply KB.wext_self; exact HS'| |].
       -- eapply KB.KRel_mono; [|exact W'|exact HK]. lia.
       -- eapply KB.SRel_down; [|exact HS']; lia.
     * intros v s'. eexists. reflexivity.
   + eapply KB.SRel_down; [|exact HS]; lia.
 - intros q kk r E1. cbn in E1. discriminate.
Qed.

Theorem chain_sound : forall C k w m g rho0i rhoi U, chain_hyps k w g rho0i rhoi ->
 chain_chk rec g0 G X g C U = true -> CRel k w X Y rho0 rho0i C rhoi U m.
Proof.
 induction C; intros k w m g rho0i rhoi U Hh E; cbn [chain_chk] in E;
  (apply orb_true_iff in E as [E|E]; [eapply chain_base; eassumption|]); try (destruct U; discriminate).
 - (* let *) destruct U as [| | | | | | | x' E' U1 | | | | | | | | | |]; try discriminate.
   repeat (apply andb_true_iff in E as [E ?]). apply text_eqb_eq in E. subst x'.
   eapply chain_let; [exact Hh|apply negb_true_iff; eassumption|apply negb_true_iff; eassumption|eassumption|].
   intros k' w' v0 v L W Hx. eapply IHC2; [exact Hx|eassumption].
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
 match goal with B : chain_chk rec g G X g C U = true |- _ => rename B into EC end.
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
   assert (Hh : chain_hyps g G Y Y' (tagged_env rho s) rho0 j w' g rho0 ((G, fr) :: rho)).
   { split; [exact Wf'|split; [apply EnvRel_cons_r; assumption|split; [apply EnvRel_cons_r; assumption|split]]].
     - cbn [lookup]. rewrite text_eqb_refl. reflexivity.
     - apply (Hr g Y Y' EY); [exact Wf'|]. unfold tagged_env. apply EnvRel_cons_r; assumption. }
   apply (chain_sound rec Hr g G X Y Y' (tagged_env rho s) rho0 C j w' 0 g rho0 ((G, fr) :: rho) U Hh EC j w' K0 K s0 (with_cell s));
    [apply le_n|eapply KB.wext_self; exact HS| |].
   + eapply KB.KRel_down; [|exact HK]; lia.
   + apply SRel_with_cell_tgt. eapply KB.SRel_down; [|exact HS]; lia.
 - intros q kk r E1. cbn in E1. discriminate.
Qed.

Theorem share_rules_sound : Forall rule_sound share_rules.
Proof. constructor; [exact share_rule_sound|constructor]. Qed.

(* check_share is sound under FrontHyps and thaw's definition in D. *)
Theorem check_share_sound : FrontHyps sealed D -> forall ps b0 b, check_share ps b0 b = true -> KRef ps b0 b.
Proof. intros FH ps b0 b E. exact (fchk_sound sealed D FH share_rules share_rules_sound _ ps b0 b E). Qed.
End Share.

(* ---------- HT is necessary: share_rule_sound fails for a D without thaw ----------
   The FrontHyps-only form of share_rule_sound holds only if FrontHyps fails at D = []. Take D = [] (D_wf holds) and the empty
   store, which meets it. The pair
       (if false 0 1)   against   (let G (freeze 1) (if false 0 (thaw G)))
   is accepted by share_rule with rec = syntactic equality in scope, a sound rec by KRef_refl (a
   FrontHyps field). The source returns 1. The target, in 9 steps, reaches (thaw G), finds no
   function thaw in the store and raises (XUndefinedFun thaw); every throw the source can reach is
   a resource error (XUser "out of memory" / "stack overflow"). KRef demands the source match the
   target's throw, so the pair is not in KRef and share_rule is not rule_sound for this D.
   SRel forces both stores to share one function table but D = [] says nothing of thaw, so no
   FrontHyps field constrains what (thaw G) does: a premise on thaw's definition in D (HT) is
   needed. share_rule_needs_thaw proves it from KRef_refl alone; share_rule_sound_needs_thaw
   restates it against the FrontHyps-only statement: that statement, at D = [], refutes
   FrontHyps sealed [], which kref-fund is to prove for every D_wf store spec. *)
Definition cx_G : name := of_string "G".
Definition cx_src : expr := EIf (EBool false) (ENum (NInt 0)) (ENum (NInt 1)).
Definition cx_tgt : expr := ELet cx_G (EFreeze (ENum (NInt 1))) (EIf (EBool false) (ENum (NInt 0)) (thaw_e cx_G)).
Definition cx_rec (g : list name) (a b : expr) : bool := expr_eqb a b && scoped g b.
Definition cx_s : store := Store [] [] [].
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
 (Cfg (Throw (XUndefinedFun thaw_name)) [] (Store [[]] [] [])).
Proof. do 9 (eapply cx_runs_tau; [reflexivity|]). constructor. Qed.

Theorem share_rule_needs_thaw : JitKRef.JitKRef.KRef_refl_statement sealed [] ->
 ~ JitFrontCheck.rule_sound sealed [] share_rule.
Proof.
 intros Hrefl H.
 assert (Hs : JitFrontCheck.chk_sound sealed [] cx_rec).
 { intros g a b E. apply andb_true_iff in E as [E1 E2]. apply expr_eqb_eq in E1. subst b.
   apply Hrefl; [split; constructor|exact E2]. }
 assert (W0 : wf_world []) by (split; constructor).
 pose proof (H cx_rec Hs [] cx_src cx_tgt cx_accepted 20%nat [] [] [] W0 (fun x I => match I with end)) as K.
 assert (HK : JitKRef.JitKRef.KRel sealed [] 20 [] [] []) by exact (JitKRefGround.JitKRefGround.KRel_top sealed [] 20 [] W0).
 assert (HS : JitKRef.JitKRef.SRel sealed [] 20 [] cx_s cx_s).
 { unfold JitKRef.JitKRef.SRel, JitKRef.JitKRef.SRel_with.
   split; [exact W0|split; [intros f d []|split; [intros f d []|split; [reflexivity|split; [constructor|]]]]].
   intros l0 l []. }
 pose proof (K 20%nat (le_n _) [] (JitKRefGround.JitKRefGround.wext_refl [] W0) [] [] HK cx_s cx_s HS) as O.
 destruct (O 9%nat [] _ ltac:(lia) cx_tgt_runs) as (_ & B & _).
 destruct (B _ _ eq_refl) as (s0 & w' & S0 & _).
 destruct (cx_inv_star _ _ _ S0 (or_introl (or_introl eq_refl))) as [I|(x & (r & Rx) & I)].
 - cbn in I. repeat destruct I as [E|I]; try discriminate; contradiction.
 - cbn in I. repeat destruct I as [E|I]; try discriminate; try contradiction.
   injection E as -> _. destruct r; discriminate.
Qed.

(* The FrontHyps-only form of share_rule_sound, at D = [], would refute FrontHyps there. *)
Corollary share_rule_sound_needs_thaw :
 (JitFrontCheck.FrontHyps sealed [] -> JitFrontCheck.rule_sound sealed [] share_rule) ->
 ~ JitFrontCheck.FrontHyps sealed [].
Proof. intros H FH. exact (share_rule_needs_thaw (JitFrontCheck.fh_refl sealed [] FH) (H FH)). Qed.
End Cx.

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
