(* Shen/JIT Phase 2, emit-spec: a test that the nested design of JitEmitRel handles REAL nested
   sub-derivations. The rules in rocq/JitEmitRule<X>.v are empty at emit-spec, so Comp_ind' in
   JitEmitRel never meets a nested derivation yet. Here a copy of the block, JitEmitRelDummy (the
   constructors of JitLowerRel indexed by code and captures, as in JitEmitRel), has one hook C_Dummy
   whose rule Rule_Dummy is NON-EMPTY: its one constructor nests three derivations of the block at
   the same code (a CompT and two Comp) and one Comp at ANOTHER code object, as a closure body is.
   Proved, all closed: Rule_Dummy_map and Rule_Dummy_all (transparent, by match), the copy's
   hand-written Comp_ind', and `suffix`, by Comp_ind': in every derivation the code after is a
   suffix of the code before. The C_Dummy case of `suffix` uses the motive of the nested
   derivations, which Comp_ind' supplies through Rule_Dummy_all.
   Does NOT say: anything about JitEmitRel itself, whose rules stay empty here; Rule_Dummy is no
   family and means nothing. *)
From Coq Require Import List ZArith NArith PArith Bool String.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitProfile JitLowerRel.
Import ListNotations.
Module JitEmitNestTest.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitLowerRel.JitLowerRel.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* The six index shapes. *)
Local Notation RelC := (B.code -> list name -> env -> N -> expr -> dest -> list B.instr -> list B.instr -> Prop).
Local Notation RelT := (B.code -> list name -> env -> N -> expr -> N -> list B.instr -> list B.instr -> Prop).
Local Notation RelO := (B.code -> list name -> env -> N -> expr -> B.operand -> N -> list B.instr -> list B.instr -> Prop).
Local Notation RelS := (B.code -> list name -> env -> N -> list expr -> list B.operand -> list B.instr -> list B.instr -> Prop).
Local Notation RelW := (B.code -> list name -> env -> N -> list expr -> list B.instr -> list B.instr -> Prop).
Local Notation RelA := (B.code -> list name -> env -> N -> N -> list expr -> list (N * N) -> list B.instr -> list B.instr -> Prop).
(* Pointwise inclusion, and the IH-carrying relation (fun i => P i /\ Q i), per shape. *)
Local Notation subC P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr), P c cv g top e d r r' -> Q c cv g top e d r r').
Local Notation subT P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r' : list B.instr), P c cv g top e l r r' -> Q c cv g top e l r r').
Local Notation subO P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r' : list B.instr), P c cv g top e o top2 r r' -> Q c cv g top e o top2 r r').
Local Notation subS P Q := (forall (c : B.code) (cv : list name) (g : env) (top : N) (es : list expr) (os : list B.operand) (r r' : list B.instr), P c cv g top es os r r' -> Q c cv g top es os r r').
Local Notation subW P Q := (forall (c : B.code) (cv : list name) (g : env) (s : N) (es : list expr) (r r' : list B.instr), P c cv g s es r r' -> Q c cv g s es r r').
Local Notation subA P Q := (forall (c : B.code) (cv : list name) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r r' : list B.instr), P c cv g s t es ms r r' -> Q c cv g s t es ms r r').
Local Notation andC P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr) => P c cv g top e d r r' /\ Q c cv g top e d r r').
Local Notation andT P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r' : list B.instr) => P c cv g top e l r r' /\ Q c cv g top e l r r').
Local Notation andO P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r' : list B.instr) => P c cv g top e o top2 r r' /\ Q c cv g top e o top2 r r').
Local Notation andS P Q := (fun (c : B.code) (cv : list name) (g : env) (top : N) (es : list expr) (os : list B.operand) (r r' : list B.instr) => P c cv g top es os r r' /\ Q c cv g top es os r r').
Local Notation andW P Q := (fun (c : B.code) (cv : list name) (g : env) (s : N) (es : list expr) (r r' : list B.instr) => P c cv g s es r r' /\ Q c cv g s es r r').
Local Notation andA P Q := (fun (c : B.code) (cv : list name) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r r' : list B.instr) => P c cv g s t es ms r r' /\ Q c cv g s t es ms r r').

(* The dummy rule: (EApp t [a; b]) at d is the test t's code, then a's and b's into d, and it also
   asks for a body e2 lowered at another code object c2. *)
Inductive Rule_Dummy (Cp : RelC) (Ct : RelT) (Co : RelO) (Cs : RelS) (Cw : RelW) (Ca : RelA) : RelC :=
 | RD_seq c cv c2 cv2 g g2 top top2 t a b e2 d l r r1 r2 r' q q' :
     Cp c2 cv2 g2 top2 e2 DRet q q' -> Ct c cv g top t l r r1 ->
     Cp c cv g top a (DSlot d) r1 r2 -> Cp c cv g top b (DSlot d) r2 r' ->
     Rule_Dummy Cp Ct Co Cs Cw Ca c cv g top (EApp t [a; b]) (DSlot d) r r'.

Definition Rule_Dummy_map (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA)
  (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr)
  (H : Rule_Dummy PC PT PO PS PW PA c cv g top e d r r') : Rule_Dummy QC QT QO QS QW QA c cv g top e d r r' :=
 match H with
 | RD_seq _ _ _ _ _ _ c cv c2 cv2 g g2 top top2 t a b e2 d l r r1 r2 r' q q' h0 h1 h2 h3 =>
     RD_seq _ _ _ _ _ _ c cv c2 cv2 g g2 top top2 t a b e2 d l r r1 r2 r' q q'
       (HC _ _ _ _ _ _ _ _ h0) (HT _ _ _ _ _ _ _ _ h1) (HC _ _ _ _ _ _ _ _ h2) (HC _ _ _ _ _ _ _ _ h3)
 end.

Definition Rule_Dummy_All (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA) : RelC :=
 Rule_Dummy (andC PC QC) (andT PT QT) (andO PO QO) (andS PS QS) (andW PW QW) (andA PA QA).

Definition Rule_Dummy_all (PC QC : RelC) (PT QT : RelT) (PO QO : RelO) (PS QS : RelS) (PW QW : RelW) (PA QA : RelA)
  (HC : subC PC QC) (HT : subT PT QT) (HO : subO PO QO) (HS : subS PS QS) (HW : subW PW QW) (HA : subA PA QA)
  (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr)
  (H : Rule_Dummy PC PT PO PS PW PA c cv g top e d r r') : Rule_Dummy_All PC QC PT QT PO QO PS QS PW QW PA QA c cv g top e d r r' :=
 match H with
 | RD_seq _ _ _ _ _ _ c cv c2 cv2 g g2 top top2 t a b e2 d l r r1 r2 r' q q' h0 h1 h2 h3 =>
     RD_seq _ _ _ _ _ _ c cv c2 cv2 g g2 top top2 t a b e2 d l r r1 r2 r' q q'
       (conj h0 (HC _ _ _ _ _ _ _ _ h0)) (conj h1 (HT _ _ _ _ _ _ _ _ h1))
       (conj h2 (HC _ _ _ _ _ _ _ _ h2)) (conj h3 (HC _ _ _ _ _ _ _ _ h3))
 end.

(* ---------- the copy, with the dummy hook ---------- *)
Module JitEmitRelDummy.
Inductive Comp : B.code -> list name -> env -> N -> expr -> dest -> list B.instr -> list B.instr -> Prop :=
 | C_lit c cv g top e v v' d k r : lit_val e = Some v -> konst c k = Some v' -> VR v v' ->
     Comp c cv g top e (DSlot d) (B.IConst d k :: r) r
 | C_move c cv g top x s d r : lookup x g = Some s -> s <> d ->
     Comp c cv g top (EVar x) (DSlot d) (B.IMove d s :: r) r
 | C_same c cv g top x d r : lookup x g = Some d -> Comp c cv g top (EVar x) (DSlot d) r r
 | C_prim c cv g top f p q args ops d r r' :
     prim_of_name f = Some p -> pmap p = Some q -> List.length args = prim_arity p -> args <> [] ->
     CompOps c cv g top args ops r (B.IPrim d q ops :: r') -> pguard c q ops = true ->
     Comp c cv g top (ECall f args) (DSlot d) r r'
 | C_let c cv g top x a b dst r r1 r' : Comp c cv g (top + 1) a (DSlot top) r r1 ->
     Comp c cv ((x, top) :: g) (top + 1) b dst r1 r' -> Comp c cv g top (ELet x a b) dst r r'
 | C_alias c cv g top x y s b dst r r' : lookup y g = Some s ->
     Comp c cv ((x, s) :: g) top b dst r r' -> Comp c cv g top (ELet x (EVar y) b) dst r r'
 | C_if_slot c cv g top t a b d l e0 r r1 r3 r' : CompT c cv g top t l r r1 ->
     Comp c cv g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> lbl c l = Some r3 ->
     Comp c cv g top b (DSlot d) r3 (B.ILabel e0 :: r') -> lbl c e0 = Some r' ->
     Comp c cv g top (EIf t a b) (DSlot d) r r'
 | C_if_ret c cv g top t a b l r r1 r3 r' : CompT c cv g top t l r r1 ->
     Comp c cv g top a DRet r1 (B.ILabel l :: r3) -> lbl c l = Some r3 -> Comp c cv g top b DRet r3 r' ->
     Comp c cv g top (EIf t a b) DRet r r'
 | C_cond_nil c cv g top d r : Comp c cv g top (ECond []) (DSlot d) (B.IPrim d B.PRaiseCond [] :: r) r
 | C_cond_true c cv g top x rest dst r r' : Comp c cv g top x dst r r' ->
     Comp c cv g top (ECond ((EBool true, x) :: rest)) dst r r'
 | C_cond_slot c cv g top t a rest d l e0 r r1 r3 r' : CompT c cv g top t l r r1 ->
     Comp c cv g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> lbl c l = Some r3 ->
     Comp c cv g top (ECond rest) (DSlot d) r3 (B.ILabel e0 :: r') -> lbl c e0 = Some r' ->
     Comp c cv g top (ECond ((t, a) :: rest)) (DSlot d) r r'
 | C_cond_ret c cv g top t a rest l r r1 r3 r' : CompT c cv g top t l r r1 ->
     Comp c cv g top a DRet r1 (B.ILabel l :: r3) -> lbl c l = Some r3 -> Comp c cv g top (ECond rest) DRet r3 r' ->
     Comp c cv g top (ECond ((t, a) :: rest)) DRet r r'
 | C_type c cv g top e dst r r' : Comp c cv g top e dst r r' -> Comp c cv g top (EType e) dst r r'
 | C_and c cv g top x y d l e0 kt kf r r1 r' : CompT c cv g top x l r r1 ->
     CompT c cv g top y l r1 (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
     konst c kt = Some (B.VBool true) -> konst c kf = Some (B.VBool false) ->
     lbl c l = Some (B.IConst d kf :: B.ILabel e0 :: r') -> lbl c e0 = Some r' ->
     Comp c cv g top (EAnd x y) (DSlot d) r r'
 | C_or c cv g top x y d l nx th e0 kt kf r r2 r' : CompT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) ->
     lbl c nx = Some r2 ->
     CompT c cv g top y l r2 (B.ILabel th :: B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
     lbl c th = Some (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
     konst c kt = Some (B.VBool true) -> konst c kf = Some (B.VBool false) ->
     lbl c l = Some (B.IConst d kf :: B.ILabel e0 :: r') -> lbl c e0 = Some r' ->
     Comp c cv g top (EOr x y) (DSlot d) r r'
 | C_ret c cv g top e o top2 r r' : CompOp c cv g top e o top2 r (B.IReturn o :: r') -> Comp c cv g top e DRet r r'
 | C_call c cv g top f args d n i r r' : not_prim_name f -> n = N.of_nat (List.length args) ->
     CompW c cv g (top + 2) args r (i :: r') -> call_instr i d top (B.sym_of_text f) n ->
     Comp c cv g top (ECall f args) (DSlot d) r r'
 | C_tail c cv g top f args n t i r r' : not_prim_name f -> n = N.of_nat (List.length args) ->
     n + 2 <= t -> top <= t -> CompTA c cv g 2 t args [] r (i :: r') ->
     tail_instr i 0 (B.sym_of_text f) n ->
     Comp c cv g top (ECall f args) DRet r r'
 (* A cons with a constant head, in place (lower.shen's value-h, from d3348ce): the tail goes to
    d, and the cons reads it there and writes d again. lower.shen takes this only when d is not a
    parameter slot, which check.shen asks of it; the simulation doesn't need that. *)
 | C_chain c cv g top f a e v v' k d r r' : prim_of_name f = Some PCons ->
     lit_val a = Some v -> konst c k = Some v' -> VR v v' ->
     Comp c cv g top e (DSlot d) r (B.IPrim d B.PCons [B.OConst k; B.OSlot d] :: r') ->
     Comp c cv g top (ECall f [a; e]) (DSlot d) r r'
 | C_Dummy c cv g top e d r r' : Rule_Dummy Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'

(* Falls through when the value is true, and goes to l when it is false. *)
with CompT : B.code -> list name -> env -> N -> expr -> N -> list B.instr -> list B.instr -> Prop :=
 | T_leaf c cv g top e o top2 l r r' : CompOp c cv g top e o top2 r (B.IJumpIfFalse o l :: r') -> CompT c cv g top e l r r'
 | T_and c cv g top x y l r r1 r' : CompT c cv g top x l r r1 -> CompT c cv g top y l r1 r' -> CompT c cv g top (EAnd x y) l r r'
 | T_or c cv g top x y l nx th r r2 r' : CompT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) ->
     lbl c nx = Some r2 -> CompT c cv g top y l r2 (B.ILabel th :: r') -> lbl c th = Some r' ->
     CompT c cv g top (EOr x y) l r r'
 | T_let c cv g top x a b l r r1 r' : Comp c cv g (top + 1) a (DSlot top) r r1 ->
     CompT c cv ((x, top) :: g) (top + 1) b l r1 r' -> CompT c cv g top (ELet x a b) l r r'
 | T_alias c cv g top x y s b l r r' : lookup y g = Some s ->
     CompT c cv ((x, s) :: g) top b l r r' -> CompT c cv g top (ELet x (EVar y) b) l r r'
 | T_type c cv g top e l r r' : CompT c cv g top e l r r' -> CompT c cv g top (EType e) l r r'

(* An operand: a variable's own slot, a constant, or the next free slot after computing it. *)
with CompOp : B.code -> list name -> env -> N -> expr -> B.operand -> N -> list B.instr -> list B.instr -> Prop :=
 | O_var c cv g top x s r : lookup x g = Some s -> s < top -> CompOp c cv g top (EVar x) (B.OSlot s) top r r
 | O_lit c cv g top e v v' k r : lit_val e = Some v -> konst c k = Some v' -> VR v v' ->
     CompOp c cv g top e (B.OConst k) top r r
 | O_val c cv g top e r r' : Comp c cv g (top + 1) e (DSlot top) r r' ->
     CompOp c cv g top e (B.OSlot top) (top + 1) r r'
 | O_type c cv g top e o top2 r r' : CompOp c cv g top e o top2 r r' -> CompOp c cv g top (EType e) o top2 r r'

with CompOps : B.code -> list name -> env -> N -> list expr -> list B.operand -> list B.instr -> list B.instr -> Prop :=
 | Os_nil c cv g top r : CompOps c cv g top [] [] r r
 | Os_cons c cv g top e es o os top2 r r1 r' : CompOp c cv g top e o top2 r r1 ->
     CompOps c cv g top2 es os r1 r' -> CompOps c cv g top (e :: es) (o :: os) r r'

(* Arguments in consecutive slots from S: a call window. *)
with CompW : B.code -> list name -> env -> N -> list expr -> list B.instr -> list B.instr -> Prop :=
 | W_nil c cv g s r : CompW c cv g s [] r r
 | W_cons c cv g s e es r r1 r' : Comp c cv g (s + 1) e (DSlot s) r r1 -> CompW c cv g (s + 1) es r1 r' ->
     CompW c cv g s (e :: es) r r'

(* A named tail call's arguments, each for parameter slot S: one already there, one computed
   into a temporary and moved last because a later argument reads S, or one computed in place,
   after which S's variables are dead. The moves are newest first, as the code emits them. *)
with CompTA : B.code -> list name -> env -> N -> N -> list expr -> list (N * N) -> list B.instr -> list B.instr -> Prop :=
 | TA_nil c cv g s t ms r' : CompTA c cv g s t [] ms (map (fun m => B.IMove (fst m) (snd m)) ms ++ r') r'
 | TA_same c cv g s t x es ms r r' : lookup x g = Some s -> CompTA c cv g (s + 1) t es ms r r' ->
     CompTA c cv g s t (EVar x :: es) ms r r'
 | TA_temp c cv g s t e es ms r r1 r' : Comp c cv g (t + 1) e (DSlot t) r r1 ->
     CompTA c cv g (s + 1) (t + 1) es ((s, t) :: ms) r1 r' -> CompTA c cv g s t (e :: es) ms r r'
 | TA_direct c cv g s t e es ms r r1 r' : Comp c cv g t e (DSlot s) r r1 ->
     CompTA c cv (kill s g) (s + 1) t es ms r1 r' -> CompTA c cv g s t (e :: es) ms r r'.



Section Ind.
Variables (PC : RelC) (PT : RelT) (PO : RelO) (PS : RelS) (PW : RelW) (PA : RelA).
Hypothesis h_C_lit : forall c cv g top e v v' d k r, lit_val e = Some v -> konst c k = Some v' -> VR v v' -> PC c cv g top e (DSlot d) (B.IConst d k :: r) r.
Hypothesis h_C_move : forall c cv g top x s d r, lookup x g = Some s -> s <> d -> PC c cv g top (EVar x) (DSlot d) (B.IMove d s :: r) r.
Hypothesis h_C_same : forall c cv g top x d r, lookup x g = Some d -> PC c cv g top (EVar x) (DSlot d) r r.
Hypothesis h_C_prim : forall c cv g top f p q args ops d r r', prim_of_name f = Some p -> pmap p = Some q -> List.length args = prim_arity p -> args <> [] -> CompOps c cv g top args ops r (B.IPrim d q ops :: r') -> PS c cv g top args ops r (B.IPrim d q ops :: r') -> pguard c q ops = true -> PC c cv g top (ECall f args) (DSlot d) r r'.
Hypothesis h_C_let : forall c cv g top x a b dst r r1 r', Comp c cv g (top + 1) a (DSlot top) r r1 -> PC c cv g (top + 1) a (DSlot top) r r1 -> Comp c cv ((x, top) :: g) (top + 1) b dst r1 r' -> PC c cv ((x, top) :: g) (top + 1) b dst r1 r' -> PC c cv g top (ELet x a b) dst r r'.
Hypothesis h_C_alias : forall c cv g top x y s b dst r r', lookup y g = Some s -> Comp c cv ((x, s) :: g) top b dst r r' -> PC c cv ((x, s) :: g) top b dst r r' -> PC c cv g top (ELet x (EVar y) b) dst r r'.
Hypothesis h_C_if_slot : forall c cv g top t a b d l e0 r r1 r3 r', CompT c cv g top t l r r1 -> PT c cv g top t l r r1 -> Comp c cv g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> PC c cv g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> lbl c l = Some r3 -> Comp c cv g top b (DSlot d) r3 (B.ILabel e0 :: r') -> PC c cv g top b (DSlot d) r3 (B.ILabel e0 :: r') -> lbl c e0 = Some r' -> PC c cv g top (EIf t a b) (DSlot d) r r'.
Hypothesis h_C_if_ret : forall c cv g top t a b l r r1 r3 r', CompT c cv g top t l r r1 -> PT c cv g top t l r r1 -> Comp c cv g top a DRet r1 (B.ILabel l :: r3) -> PC c cv g top a DRet r1 (B.ILabel l :: r3) -> lbl c l = Some r3 -> Comp c cv g top b DRet r3 r' -> PC c cv g top b DRet r3 r' -> PC c cv g top (EIf t a b) DRet r r'.
Hypothesis h_C_cond_nil : forall c cv g top d r, PC c cv g top (ECond []) (DSlot d) (B.IPrim d B.PRaiseCond [] :: r) r.
Hypothesis h_C_cond_true : forall c cv g top x rest dst r r', Comp c cv g top x dst r r' -> PC c cv g top x dst r r' -> PC c cv g top (ECond ((EBool true, x) :: rest)) dst r r'.
Hypothesis h_C_cond_slot : forall c cv g top t a rest d l e0 r r1 r3 r', CompT c cv g top t l r r1 -> PT c cv g top t l r r1 -> Comp c cv g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> PC c cv g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> lbl c l = Some r3 -> Comp c cv g top (ECond rest) (DSlot d) r3 (B.ILabel e0 :: r') -> PC c cv g top (ECond rest) (DSlot d) r3 (B.ILabel e0 :: r') -> lbl c e0 = Some r' -> PC c cv g top (ECond ((t, a) :: rest)) (DSlot d) r r'.
Hypothesis h_C_cond_ret : forall c cv g top t a rest l r r1 r3 r', CompT c cv g top t l r r1 -> PT c cv g top t l r r1 -> Comp c cv g top a DRet r1 (B.ILabel l :: r3) -> PC c cv g top a DRet r1 (B.ILabel l :: r3) -> lbl c l = Some r3 -> Comp c cv g top (ECond rest) DRet r3 r' -> PC c cv g top (ECond rest) DRet r3 r' -> PC c cv g top (ECond ((t, a) :: rest)) DRet r r'.
Hypothesis h_C_type : forall c cv g top e dst r r', Comp c cv g top e dst r r' -> PC c cv g top e dst r r' -> PC c cv g top (EType e) dst r r'.
Hypothesis h_C_and : forall c cv g top x y d l e0 kt kf r r1 r', CompT c cv g top x l r r1 -> PT c cv g top x l r r1 -> CompT c cv g top y l r1 (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') -> PT c cv g top y l r1 (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') -> konst c kt = Some (B.VBool true) -> konst c kf = Some (B.VBool false) -> lbl c l = Some (B.IConst d kf :: B.ILabel e0 :: r') -> lbl c e0 = Some r' -> PC c cv g top (EAnd x y) (DSlot d) r r'.
Hypothesis h_C_or : forall c cv g top x y d l nx th e0 kt kf r r2 r', CompT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) -> PT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) -> lbl c nx = Some r2 -> CompT c cv g top y l r2 (B.ILabel th :: B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') -> PT c cv g top y l r2 (B.ILabel th :: B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') -> lbl c th = Some (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') -> konst c kt = Some (B.VBool true) -> konst c kf = Some (B.VBool false) -> lbl c l = Some (B.IConst d kf :: B.ILabel e0 :: r') -> lbl c e0 = Some r' -> PC c cv g top (EOr x y) (DSlot d) r r'.
Hypothesis h_C_ret : forall c cv g top e o top2 r r', CompOp c cv g top e o top2 r (B.IReturn o :: r') -> PO c cv g top e o top2 r (B.IReturn o :: r') -> PC c cv g top e DRet r r'.
Hypothesis h_C_call : forall c cv g top f args d n i r r', not_prim_name f -> n = N.of_nat (List.length args) -> CompW c cv g (top + 2) args r (i :: r') -> PW c cv g (top + 2) args r (i :: r') -> call_instr i d top (B.sym_of_text f) n -> PC c cv g top (ECall f args) (DSlot d) r r'.
Hypothesis h_C_tail : forall c cv g top f args n t i r r', not_prim_name f -> n = N.of_nat (List.length args) -> n + 2 <= t -> top <= t -> CompTA c cv g 2 t args [] r (i :: r') -> PA c cv g 2 t args [] r (i :: r') -> tail_instr i 0 (B.sym_of_text f) n -> PC c cv g top (ECall f args) DRet r r'.
Hypothesis h_C_chain : forall c cv g top f a e v v' k d r r', prim_of_name f = Some PCons -> lit_val a = Some v -> konst c k = Some v' -> VR v v' -> Comp c cv g top e (DSlot d) r (B.IPrim d B.PCons [B.OConst k; B.OSlot d] :: r') -> PC c cv g top e (DSlot d) r (B.IPrim d B.PCons [B.OConst k; B.OSlot d] :: r') -> PC c cv g top (ECall f [a; e]) (DSlot d) r r'.
Hypothesis h_C_Dummy : forall c cv g top e d r r', Rule_Dummy Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Rule_Dummy_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_T_leaf : forall c cv g top e o top2 l r r', CompOp c cv g top e o top2 r (B.IJumpIfFalse o l :: r') -> PO c cv g top e o top2 r (B.IJumpIfFalse o l :: r') -> PT c cv g top e l r r'.
Hypothesis h_T_and : forall c cv g top x y l r r1 r', CompT c cv g top x l r r1 -> PT c cv g top x l r r1 -> CompT c cv g top y l r1 r' -> PT c cv g top y l r1 r' -> PT c cv g top (EAnd x y) l r r'.
Hypothesis h_T_or : forall c cv g top x y l nx th r r2 r', CompT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) -> PT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) -> lbl c nx = Some r2 -> CompT c cv g top y l r2 (B.ILabel th :: r') -> PT c cv g top y l r2 (B.ILabel th :: r') -> lbl c th = Some r' -> PT c cv g top (EOr x y) l r r'.
Hypothesis h_T_let : forall c cv g top x a b l r r1 r', Comp c cv g (top + 1) a (DSlot top) r r1 -> PC c cv g (top + 1) a (DSlot top) r r1 -> CompT c cv ((x, top) :: g) (top + 1) b l r1 r' -> PT c cv ((x, top) :: g) (top + 1) b l r1 r' -> PT c cv g top (ELet x a b) l r r'.
Hypothesis h_T_alias : forall c cv g top x y s b l r r', lookup y g = Some s -> CompT c cv ((x, s) :: g) top b l r r' -> PT c cv ((x, s) :: g) top b l r r' -> PT c cv g top (ELet x (EVar y) b) l r r'.
Hypothesis h_T_type : forall c cv g top e l r r', CompT c cv g top e l r r' -> PT c cv g top e l r r' -> PT c cv g top (EType e) l r r'.
Hypothesis h_O_var : forall c cv g top x s r, lookup x g = Some s -> s < top -> PO c cv g top (EVar x) (B.OSlot s) top r r.
Hypothesis h_O_lit : forall c cv g top e v v' k r, lit_val e = Some v -> konst c k = Some v' -> VR v v' -> PO c cv g top e (B.OConst k) top r r.
Hypothesis h_O_val : forall c cv g top e r r', Comp c cv g (top + 1) e (DSlot top) r r' -> PC c cv g (top + 1) e (DSlot top) r r' -> PO c cv g top e (B.OSlot top) (top + 1) r r'.
Hypothesis h_O_type : forall c cv g top e o top2 r r', CompOp c cv g top e o top2 r r' -> PO c cv g top e o top2 r r' -> PO c cv g top (EType e) o top2 r r'.
Hypothesis h_Os_nil : forall c cv g top r, PS c cv g top [] [] r r.
Hypothesis h_Os_cons : forall c cv g top e es o os top2 r r1 r', CompOp c cv g top e o top2 r r1 -> PO c cv g top e o top2 r r1 -> CompOps c cv g top2 es os r1 r' -> PS c cv g top2 es os r1 r' -> PS c cv g top (e :: es) (o :: os) r r'.
Hypothesis h_W_nil : forall c cv g s r, PW c cv g s [] r r.
Hypothesis h_W_cons : forall c cv g s e es r r1 r', Comp c cv g (s + 1) e (DSlot s) r r1 -> PC c cv g (s + 1) e (DSlot s) r r1 -> CompW c cv g (s + 1) es r1 r' -> PW c cv g (s + 1) es r1 r' -> PW c cv g s (e :: es) r r'.
Hypothesis h_TA_nil : forall c cv g s t ms r', PA c cv g s t [] ms (map (fun m => B.IMove (fst m) (snd m)) ms ++ r') r'.
Hypothesis h_TA_same : forall c cv g s t x es ms r r', lookup x g = Some s -> CompTA c cv g (s + 1) t es ms r r' -> PA c cv g (s + 1) t es ms r r' -> PA c cv g s t (EVar x :: es) ms r r'.
Hypothesis h_TA_temp : forall c cv g s t e es ms r r1 r', Comp c cv g (t + 1) e (DSlot t) r r1 -> PC c cv g (t + 1) e (DSlot t) r r1 -> CompTA c cv g (s + 1) (t + 1) es ((s, t) :: ms) r1 r' -> PA c cv g (s + 1) (t + 1) es ((s, t) :: ms) r1 r' -> PA c cv g s t (e :: es) ms r r'.
Hypothesis h_TA_direct : forall c cv g s t e es ms r r1 r', Comp c cv g t e (DSlot s) r r1 -> PC c cv g t e (DSlot s) r r1 -> CompTA c cv (kill s g) (s + 1) t es ms r1 r' -> PA c cv (kill s g) (s + 1) t es ms r1 r' -> PA c cv g s t (e :: es) ms r r'.

Fixpoint Comp_ind' c cv g top e d r r' (H : Comp c cv g top e d r r') {struct H} : PC c cv g top e d r r' :=
 match H with
 | C_lit c cv g top e v v' d k r H0 H1 H2 => h_C_lit c cv g top e v v' d k r H0 H1 H2
 | C_move c cv g top x s d r H0 H1 => h_C_move c cv g top x s d r H0 H1
 | C_same c cv g top x d r H0 => h_C_same c cv g top x d r H0
 | C_prim c cv g top f p q args ops d r r' H0 H1 H2 H3 H4 H5 => h_C_prim c cv g top f p q args ops d r r' H0 H1 H2 H3 H4 (CompOps_ind' _ _ _ _ _ _ _ _ H4) H5
 | C_let c cv g top x a b dst r r1 r' H0 H1 => h_C_let c cv g top x a b dst r r1 r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0) H1 (Comp_ind' _ _ _ _ _ _ _ _ H1)
 | C_alias c cv g top x y s b dst r r' H0 H1 => h_C_alias c cv g top x y s b dst r r' H0 H1 (Comp_ind' _ _ _ _ _ _ _ _ H1)
 | C_if_slot c cv g top t a b d l e0 r r1 r3 r' H0 H1 H2 H3 H4 => h_C_if_slot c cv g top t a b d l e0 r r1 r3 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 (Comp_ind' _ _ _ _ _ _ _ _ H1) H2 H3 (Comp_ind' _ _ _ _ _ _ _ _ H3) H4
 | C_if_ret c cv g top t a b l r r1 r3 r' H0 H1 H2 H3 => h_C_if_ret c cv g top t a b l r r1 r3 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 (Comp_ind' _ _ _ _ _ _ _ _ H1) H2 H3 (Comp_ind' _ _ _ _ _ _ _ _ H3)
 | C_cond_nil c cv g top d r  => h_C_cond_nil c cv g top d r 
 | C_cond_true c cv g top x rest dst r r' H0 => h_C_cond_true c cv g top x rest dst r r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0)
 | C_cond_slot c cv g top t a rest d l e0 r r1 r3 r' H0 H1 H2 H3 H4 => h_C_cond_slot c cv g top t a rest d l e0 r r1 r3 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 (Comp_ind' _ _ _ _ _ _ _ _ H1) H2 H3 (Comp_ind' _ _ _ _ _ _ _ _ H3) H4
 | C_cond_ret c cv g top t a rest l r r1 r3 r' H0 H1 H2 H3 => h_C_cond_ret c cv g top t a rest l r r1 r3 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 (Comp_ind' _ _ _ _ _ _ _ _ H1) H2 H3 (Comp_ind' _ _ _ _ _ _ _ _ H3)
 | C_type c cv g top e dst r r' H0 => h_C_type c cv g top e dst r r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0)
 | C_and c cv g top x y d l e0 kt kf r r1 r' H0 H1 H2 H3 H4 H5 => h_C_and c cv g top x y d l e0 kt kf r r1 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 (CompT_ind' _ _ _ _ _ _ _ _ H1) H2 H3 H4 H5
 | C_or c cv g top x y d l nx th e0 kt kf r r2 r' H0 H1 H2 H3 H4 H5 H6 H7 => h_C_or c cv g top x y d l nx th e0 kt kf r r2 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 H2 (CompT_ind' _ _ _ _ _ _ _ _ H2) H3 H4 H5 H6 H7
 | C_ret c cv g top e o top2 r r' H0 => h_C_ret c cv g top e o top2 r r' H0 (CompOp_ind' _ _ _ _ _ _ _ _ _ H0)
 | C_call c cv g top f args d n i r r' H0 H1 H2 H3 => h_C_call c cv g top f args d n i r r' H0 H1 H2 (CompW_ind' _ _ _ _ _ _ _ H2) H3
 | C_tail c cv g top f args n t i r r' H0 H1 H2 H3 H4 H5 => h_C_tail c cv g top f args n t i r r' H0 H1 H2 H3 H4 (CompTA_ind' _ _ _ _ _ _ _ _ _ H4) H5
 | C_chain c cv g top f a e v v' k d r r' H0 H1 H2 H3 H4 => h_C_chain c cv g top f a e v v' k d r r' H0 H1 H2 H3 H4 (Comp_ind' _ _ _ _ _ _ _ _ H4)
 | C_Dummy c cv g top e d r r' H0 => h_C_Dummy c cv g top e d r r' H0 (Rule_Dummy_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 end
with CompT_ind' c cv g top e l r r' (H : CompT c cv g top e l r r') {struct H} : PT c cv g top e l r r' :=
 match H with
 | T_leaf c cv g top e o top2 l r r' H0 => h_T_leaf c cv g top e o top2 l r r' H0 (CompOp_ind' _ _ _ _ _ _ _ _ _ H0)
 | T_and c cv g top x y l r r1 r' H0 H1 => h_T_and c cv g top x y l r r1 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 (CompT_ind' _ _ _ _ _ _ _ _ H1)
 | T_or c cv g top x y l nx th r r2 r' H0 H1 H2 H3 => h_T_or c cv g top x y l nx th r r2 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 H2 (CompT_ind' _ _ _ _ _ _ _ _ H2) H3
 | T_let c cv g top x a b l r r1 r' H0 H1 => h_T_let c cv g top x a b l r r1 r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0) H1 (CompT_ind' _ _ _ _ _ _ _ _ H1)
 | T_alias c cv g top x y s b l r r' H0 H1 => h_T_alias c cv g top x y s b l r r' H0 H1 (CompT_ind' _ _ _ _ _ _ _ _ H1)
 | T_type c cv g top e l r r' H0 => h_T_type c cv g top e l r r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0)
 end
with CompOp_ind' c cv g top e o top2 r r' (H : CompOp c cv g top e o top2 r r') {struct H} : PO c cv g top e o top2 r r' :=
 match H with
 | O_var c cv g top x s r H0 H1 => h_O_var c cv g top x s r H0 H1
 | O_lit c cv g top e v v' k r H0 H1 H2 => h_O_lit c cv g top e v v' k r H0 H1 H2
 | O_val c cv g top e r r' H0 => h_O_val c cv g top e r r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0)
 | O_type c cv g top e o top2 r r' H0 => h_O_type c cv g top e o top2 r r' H0 (CompOp_ind' _ _ _ _ _ _ _ _ _ H0)
 end
with CompOps_ind' c cv g top es os r r' (H : CompOps c cv g top es os r r') {struct H} : PS c cv g top es os r r' :=
 match H with
 | Os_nil c cv g top r  => h_Os_nil c cv g top r 
 | Os_cons c cv g top e es o os top2 r r1 r' H0 H1 => h_Os_cons c cv g top e es o os top2 r r1 r' H0 (CompOp_ind' _ _ _ _ _ _ _ _ _ H0) H1 (CompOps_ind' _ _ _ _ _ _ _ _ H1)
 end
with CompW_ind' c cv g s es r r' (H : CompW c cv g s es r r') {struct H} : PW c cv g s es r r' :=
 match H with
 | W_nil c cv g s r  => h_W_nil c cv g s r 
 | W_cons c cv g s e es r r1 r' H0 H1 => h_W_cons c cv g s e es r r1 r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0) H1 (CompW_ind' _ _ _ _ _ _ _ H1)
 end
with CompTA_ind' c cv g s t es ms r r' (H : CompTA c cv g s t es ms r r') {struct H} : PA c cv g s t es ms r r' :=
 match H with
 | TA_nil c cv g s t ms r'  => h_TA_nil c cv g s t ms r' 
 | TA_same c cv g s t x es ms r r' H0 H1 => h_TA_same c cv g s t x es ms r r' H0 H1 (CompTA_ind' _ _ _ _ _ _ _ _ _ H1)
 | TA_temp c cv g s t e es ms r r1 r' H0 H1 => h_TA_temp c cv g s t e es ms r r1 r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0) H1 (CompTA_ind' _ _ _ _ _ _ _ _ _ H1)
 | TA_direct c cv g s t e es ms r r1 r' H0 H1 => h_TA_direct c cv g s t e es ms r r1 r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0) H1 (CompTA_ind' _ _ _ _ _ _ _ _ _ H1)
 end.

End Ind.

(* ---------- a lemma by Comp_ind' ---------- *)
Definition Suf (r' r : list B.instr) : Prop := exists p, r = p ++ r'.
Lemma suf_refl : forall r, Suf r r.
Proof. intro r. exists []. reflexivity. Qed.
Lemma suf_cons : forall r' i r, Suf r' r -> Suf r' (i :: r).
Proof. intros r' i r [p ->]. exists (i :: p). reflexivity. Qed.
Lemma suf_app : forall r' p r, Suf r' r -> Suf r' (p ++ r).
Proof. intros r' p r [q ->]. exists (p ++ q). rewrite app_assoc. reflexivity. Qed.
Ltac suf_close :=
 repeat match goal with H : Suf _ _ |- _ => destruct H as [? ->] end;
 repeat first [apply suf_refl | apply suf_app | apply suf_cons].

(* The code after any derivation is a suffix of the code before it. *)
Theorem suffix :
 (forall c cv g top e d r r', Comp c cv g top e d r r' -> Suf r' r) /\
 (forall c cv g top e l r r', CompT c cv g top e l r r' -> Suf r' r) /\
 (forall c cv g top e o top2 r r', CompOp c cv g top e o top2 r r' -> Suf r' r) /\
 (forall c cv g top es os r r', CompOps c cv g top es os r r' -> Suf r' r) /\
 (forall c cv g s es r r', CompW c cv g s es r r' -> Suf r' r) /\
 (forall c cv g s t es ms r r', CompTA c cv g s t es ms r r' -> Suf r' r).
Proof.
 pose (PC := fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (d : dest) (r r' : list B.instr) => Suf r' r).
 pose (PT := fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (l : N) (r r' : list B.instr) => Suf r' r).
 pose (PO := fun (c : B.code) (cv : list name) (g : env) (top : N) (e : expr) (o : B.operand) (top2 : N) (r r' : list B.instr) => Suf r' r).
 pose (PS := fun (c : B.code) (cv : list name) (g : env) (top : N) (es : list expr) (os : list B.operand) (r r' : list B.instr) => Suf r' r).
 pose (PW := fun (c : B.code) (cv : list name) (g : env) (s : N) (es : list expr) (r r' : list B.instr) => Suf r' r).
 pose (PA := fun (c : B.code) (cv : list name) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r r' : list B.instr) => Suf r' r).
 assert (D : forall c cv g top e d r r', Rule_Dummy_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> Suf r' r).
 { intros c cv g top e d r r' H. destruct H as [c cv c2 cv2 g g2 top top2 t a b e2 d l r r1 r2 r' q q' _ [_ I1] [_ I2] [_ I3]].
   unfold PT, PC in *. suf_close. }
 repeat split; intros;
 [ eapply (Comp_ind' PC PT PO PS PW PA) | eapply (CompT_ind' PC PT PO PS PW PA) | eapply (CompOp_ind' PC PT PO PS PW PA)
 | eapply (CompOps_ind' PC PT PO PS PW PA) | eapply (CompW_ind' PC PT PO PS PW PA) | eapply (CompTA_ind' PC PT PO PS PW PA) ];
 try eassumption; unfold PC, PT, PO, PS, PW, PA; intros; try (eapply D; eassumption); suf_close.
Qed.
End JitEmitRelDummy.
End JitEmitNestTest.
