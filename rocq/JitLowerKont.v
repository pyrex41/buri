(* Shen/JIT Phase 2: the continuation relation behind the simulation in JitLowerSim.v, and what
   writes to the stack leave intact. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel.
Import ListNotations.
Module JitLowerKont.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort JitLowerRel.JitLowerRel.
Local Open Scope N_scope.

(* ---------- stack facts ---------- *)
Definition slotv (st : B.tree B.val) (a : N) : option B.val := B.tget (B.skey a) st.

Lemma skey_inj : forall a b, B.skey a = B.skey b -> a = b.
Proof.
 intros a b H. unfold B.skey in H.
 pose proof (N.succ_pos_spec a) as A. pose proof (N.succ_pos_spec b) as Bb.
 rewrite H in A. apply N.succ_inj. congruence.
Qed.
Lemma slotv_same : forall st a v, slotv (B.tset (B.skey a) v st) a = Some v.
Proof. intros. apply JitMeta.JitMeta.tget_tset_same. Qed.
Lemma slotv_other : forall st a b v, a <> b -> slotv (B.tset (B.skey b) v st) a = slotv st a.
Proof.
 intros. unfold slotv. apply JitMeta.JitMeta.tget_tset_other.
 intro E; apply H; apply skey_inj; auto.
Qed.

Definition MEnv (fp : N) (st : B.tree B.val) (g : env) (rho : lenv) : Prop :=
 forall x s, lookup x g = Some s -> exists v v',
   lookup x rho = Some v /\ slotv st (fp + s) = Some v' /\ VR v v'.
Definition EnvBelow (g : env) (top : N) := forall x s, lookup x g = Some s -> s < top.
Definition Prot (g : env) (fp : N) (w : N -> Prop) := forall x s, lookup x g = Some s -> ~ w (fp + s).
Definition Above (fp top : N) (w : N -> Prop) := forall a, fp + top <= a -> w a.
Definition Sub (w w1 : N -> Prop) := forall a, w a -> w1 a.

Definition read_o (c : B.code) (fp : N) (st : B.tree B.val) (o : B.operand) : option B.val :=
 match o with
 | B.OSlot s => slotv st (fp + s)
 | B.OConst k => nth_error (B.code_consts c) (N.to_nat k) end.
Definition o_safe (fp : N) (w : N -> Prop) (o : B.operand) : Prop :=
 match o with B.OSlot s => ~ w (fp + s) | B.OConst _ => True end.
Definition o_below (top : N) (o : B.operand) : Prop :=
 match o with B.OSlot s => s < top | B.OConst _ => True end.

(* Operands already delivered, newest first. *)
Inductive DoneR (c : B.code) (fp : N) (st : B.tree B.val) : list value -> list B.operand -> Prop :=
 | DR_nil : DoneR c fp st [] []
 | DR_cons v v' o vs os : read_o c fp st o = Some v' -> VR v v' -> DoneR c fp st vs os ->
     DoneR c fp st (v :: vs) (o :: os).

(* Values in consecutive slots from address a. *)
Inductive ArgsAt (st : B.tree B.val) : N -> list value -> Prop :=
 | AA_nil a : ArgsAt st a []
 | AA_cons a v v' vs : slotv st a = Some v' -> VR v v' -> ArgsAt st (a + 1) vs -> ArgsAt st a (v :: vs).

(* Where parameter slot i's value is before the pending moves run. *)
Fixpoint loc (ms : list (N * N)) (i : N) : N := match ms with
 | [] => i | (s, t) :: ms => if N.eqb s i then t else loc ms i end.

(* Delivered tail-call arguments for slots from i, oldest first. *)
Inductive ParamAt (fp : N) (st : B.tree B.val) (ms : list (N * N)) : N -> list value -> Prop :=
 | PA_nil i : ParamAt fp st ms i []
 | PA_cons i v v' vs : slotv st (fp + loc ms i) = Some v' -> VR v v' ->
     ParamAt fp st ms (i + 1) vs -> ParamAt fp st ms i (v :: vs).

(* What receives a value: the source's frames against the code still to run. `w` is where the
   running code may write without disturbing any of it. *)
Inductive KD : B.code -> N -> B.tree B.val -> list B.cont -> (N -> Prop) -> B.operand ->
    list B.instr -> list frame -> Prop :=
 | KD_ret c fp st cs w o r k : Sub w (fun a => fp <= a) -> RK fp st cs k ->
     KD c fp st cs w o (B.IReturn o :: r) k
 | KD_jump c fp st cs w o e r r1 k : lbl c e = Some r1 -> KD c fp st cs w o r1 k ->
     KD c fp st cs w o (B.IJump e :: r) k
 | KD_label c fp st cs w o l r k : KD c fp st cs w o r k -> KD c fp st cs w o (B.ILabel l :: r) k
 | KD_let c fp st cs w d r x b rho k1 g top dst r2 w1 :
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g top -> d < top ->
     Comp c ((x, d) :: g) top b dst r r2 -> Sub w w1 -> Above fp top w1 ->
     KC c fp st cs w1 dst r2 k1 ->
     KD c fp st cs w (B.OSlot d) r (KLet x b rho :: k1)
 | KD_lett c fp st cs w d r x b rho k1 g top l r2 w1 :
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g top -> d < top ->
     CompT c ((x, d) :: g) top b l r r2 -> Sub w w1 -> Above fp top w1 ->
     TK c fp st cs w1 true l r2 k1 ->
     KD c fp st cs w (B.OSlot d) r (KLet x b rho :: k1)
 | KD_test c fp st cs w o l r k : TK c fp st cs w true l r k ->
     KD c fp st cs w o (B.IJumpIfFalse o l :: r) k
 | KD_prim c fp st cs w o r f p q vals es rho k1 g top ops dops d r1 w1 :
     prim_of_name f = Some p -> pmap p = Some q ->
     (List.length vals + 1 + List.length es)%nat = prim_arity p ->
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g top ->
     CompOps c g top es ops r (B.IPrim d q (rev dops ++ o :: ops) :: r1) ->
     DoneR c fp st vals dops -> Forall (o_safe fp w) dops ->
     Forall (o_below top) dops -> o_below top o ->
     Sub w w1 -> Above fp top w1 -> w1 (fp + d) -> KD c fp st cs w1 (B.OSlot d) r1 k1 ->
     KD c fp st cs w o r (KCallArgs f vals es rho :: k1)
 | KD_call c fp st cs w r f vals es rho k1 g a s d n i r1 w1 :
     not_prim_name f -> s = a + 2 + N.of_nat (List.length vals) ->
     n = N.of_nat (List.length vals + 1 + List.length es) ->
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g (s + 1) ->
     CompW c g (s + 1) es r (i :: r1) -> call_instr i d a (B.sym_of_text f) n ->
     ArgsAt st (fp + a + 2) (rev vals) -> Sub w (fun x => fp + s <= x) ->
     Sub w w1 -> Above fp a w1 -> w1 (fp + d) -> KD c fp st cs w1 (B.OSlot d) r1 k1 ->
     KD c fp st cs w (B.OSlot s) r (KCallArgs f vals es rho :: k1)
 | KD_tail c fp st cs w o r f vals es rho k1 g s t t0 ms n i r1 :
     not_prim_name f -> s = 2 + N.of_nat (List.length vals) ->
     n = N.of_nat (List.length vals + 1 + List.length es) -> n + 2 <= t0 -> t0 <= t ->
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g t ->
     CompTA c g (s + 1) t es ms r (i :: r1) -> tail_instr i 0 (B.sym_of_text f) n ->
     o = B.OSlot (loc ms s) -> loc ms s < t ->
     Forall (fun m => 2 <= fst m < s + 1 /\ n + 2 <= snd m < t) ms -> NoDup (map fst ms) ->
     (forall j, 2 <= j < s -> loc ms j = j \/ n + 2 <= loc ms j < t0) ->
     ParamAt fp st ms 2 (rev vals) ->
     Sub w (fun x => x = fp + s \/ fp + t0 <= x) -> RK fp st cs k1 ->
     KD c fp st cs w o r (KCallArgs f vals es rho :: k1)

with TK : B.code -> N -> B.tree B.val -> list B.cont -> (N -> Prop) -> bool -> N ->
    list B.instr -> list frame -> Prop :=
 | TK_if c fp st cs w l r a b rho k1 g top dst r2 r3 r4 w1 :
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g top ->
     Comp c g top a dst r r2 -> lbl c l = Some r3 -> Comp c g top b dst r3 r4 ->
     Sub w w1 -> Above fp top w1 -> KC c fp st cs w1 dst r2 k1 -> KC c fp st cs w1 dst r4 k1 ->
     TK c fp st cs w true l r (KIf a b rho :: k1)
 | TK_cond c fp st cs w l r a rest rho k1 g top dst r2 r3 r4 w1 :
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g top ->
     Comp c g top a dst r r2 -> lbl c l = Some r3 -> Comp c g top (ECond rest) dst r3 r4 ->
     Sub w w1 -> Above fp top w1 -> KC c fp st cs w1 dst r2 k1 -> KC c fp st cs w1 dst r4 k1 ->
     TK c fp st cs w true l r (KCond a rest rho :: k1)
 | TK_and c fp st cs w gd l r y rho k1 g top r2 w1 :
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g top ->
     CompT c g top y l r r2 -> Sub w w1 -> Above fp top w1 ->
     TK c fp st cs w1 gd l r2 k1 ->
     TK c fp st cs w true l r (KAnd y rho :: k1)
 | TK_andr c fp st cs w gd l r k1 w1 : Sub w w1 -> TK c fp st cs w1 gd l r k1 ->
     TK c fp st cs w true l r (KAndR :: k1)
 | TK_or c fp st cs w gd l nx r1 y rho k1 g top r2 r3 w1 :
     MEnv fp st g rho -> Prot g fp w -> EnvBelow g top ->
     lbl c nx = Some r2 -> CompT c g top y l r2 r3 -> Sub w w1 -> Above fp top w1 ->
     TK c fp st cs w1 gd l r3 k1 -> TK c fp st cs w1 gd l r1 k1 ->
     TK c fp st cs w true nx r1 (KOr y rho :: k1)
 | TK_orr c fp st cs w gd l r k1 w1 : Sub w w1 -> TK c fp st cs w1 gd l r k1 ->
     TK c fp st cs w true l r (KOrR :: k1)
 | TK_jump c fp st cs w gd l e r r1 k : lbl c e = Some r1 -> TK c fp st cs w gd l r1 k ->
     TK c fp st cs w gd l (B.IJump e :: r) k
 | TK_label c fp st cs w gd l x r k : TK c fp st cs w gd l r k ->
     TK c fp st cs w gd l (B.ILabel x :: r) k
 | TK_value c fp st cs w l d kt kf r2 r4 k w1 :
     konst c kt = Some (B.VBool true) -> konst c kf = Some (B.VBool false) ->
     lbl c l = Some (B.IConst d kf :: r4) -> Sub w w1 -> w1 (fp + d) ->
     KD c fp st cs w1 (B.OSlot d) r2 k -> KD c fp st cs w1 (B.OSlot d) r4 k ->
     TK c fp st cs w false l (B.IConst d kt :: r2) k

with KC : B.code -> N -> B.tree B.val -> list B.cont -> (N -> Prop) -> dest ->
    list B.instr -> list frame -> Prop :=
 | KC_ret c fp st cs w r k : Sub w (fun a => fp <= a) -> RK fp st cs k -> KC c fp st cs w DRet r k
 | KC_slot c fp st cs w d r k : w (fp + d) -> KD c fp st cs w (B.OSlot d) r k ->
     KC c fp st cs w (DSlot d) r k

(* The function's own continuation: the caller's code, through a saved frame. *)
with RK : N -> B.tree B.val -> list B.cont -> list frame -> Prop :=
 | RK_top fp st : RK fp st [] []
 | RK_call fp st c r d a cs k w : a <= fp -> Above (fp - a) a w ->
     KD c (fp - a) st cs w (B.OSlot d) r k -> w (fp - a + d) ->
     RK fp st (B.Cont c r d a :: cs) k.

Scheme KD_m := Induction for KD Sort Prop
 with TK_m := Induction for TK Sort Prop
 with KC_m := Induction for KC Sort Prop
 with RK_m := Induction for RK Sort Prop.
Combined Scheme K_mut from KD_m, TK_m, KC_m, RK_m.

End JitLowerKont.
