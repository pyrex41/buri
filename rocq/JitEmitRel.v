(* Shen/JIT Phase 2, the extended emission relation (task emit-spec). JitLowerRel's Comp, CompT,
   CompOp, CompOps, CompW and CompTA, copied constructor for constructor, with two changes:
   - Every relation is indexed by the code object c and the code's capture names cv in front of
     JitLowerRel's indices. JitLowerRel has c as a Section variable (a uniform parameter). Here it
     is an index, because a closure's body is lowered as NESTED code (code_codes c), and the Clo
     family must state that body's Comp at the nested code object inside the same derivation.
     With c uniform this needs a second inductive over codes nested through Comp's own parameter,
     and Rocq refuses that ("Non strictly positive occurrence", spike Exp.v in the task report).
     cv lists the variables the code reads from its closure (slot 1) with ICapture, numbered as
     lower.shen's capture-index numbers them; it is [] for a top-level function. No constructor
     copied from JitLowerRel reads cv.
   - One hook per emission family X in Eq, Store, Prim, DoFold, Clo, App, Trap, and per judgement:
     C_X (Comp), T_X (CompT) and O_X (CompOp), each taking a derivation of the family's
     Rule_X / RuleT_X / RuleO_X (rocq/JitEmitRule<X>.v) over the six relations of this block,
     which occur there strictly positively (a nested inductive through a parameter). All 21 rules
     are empty at emit-spec; a family adds constructors in its own file only. The CompT and CompOp
     hooks are there because lower.shen's `test` lowers (do X Y) as value-X-then-test-Y, and its
     `operand` lowers a folded constant list as (const K) with no code.
   Rocq derives no useful induction principle for a nested block, so Comp_ind' (one Fixpoint per
   relation, mutually) is written by hand. It recurses through each family's rule with that
   family's *_all lemma only, so it does not change when a family adds constructors, provided the
   family keeps its *_all transparent. Downstream proofs use Comp_ind' and never invert a Rule_X
   outside its own file.
   Proved here: Comp_ind' (closed), comp_embed (JitLowerRel's derivations embed, closed).
   Does NOT say: anything about the semantics of the code (JitEmitInv states that), or that
   lower.shen's output is accepted (the family checkers, emit-check, decide that per definition). *)
From Coq Require Import List ZArith NArith PArith Bool String.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitProfile JitLowerRel JitEmitRuleEq JitEmitRuleStore JitEmitRulePrim JitEmitRuleDoFold JitEmitRuleClo JitEmitRuleApp JitEmitRuleTrap.
Import ListNotations.
Module JitEmitRel.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitLowerRel.JitLowerRel.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* The relations of JitLowerRel.v:82-160, indexed by (c, cv), with the family hooks at the end
   of Comp, CompT and CompOp. Comments are JitLowerRel's. *)
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
 | C_Eq c cv g top e d r r' : JitEmitRuleEq.Rule_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'
 | C_Store c cv g top e d r r' : JitEmitRuleStore.Rule_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'
 | C_Prim c cv g top e d r r' : JitEmitRulePrim.Rule_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'
 | C_DoFold c cv g top e d r r' : JitEmitRuleDoFold.Rule_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'
 | C_Clo c cv g top e d r r' : JitEmitRuleClo.Rule_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'
 | C_App c cv g top e d r r' : JitEmitRuleApp.Rule_App Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'
 | C_Trap c cv g top e d r r' : JitEmitRuleTrap.Rule_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> Comp c cv g top e d r r'

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
 | T_Eq c cv g top e l r r' : JitEmitRuleEq.RuleT_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'
 | T_Store c cv g top e l r r' : JitEmitRuleStore.RuleT_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'
 | T_Prim c cv g top e l r r' : JitEmitRulePrim.RuleT_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'
 | T_DoFold c cv g top e l r r' : JitEmitRuleDoFold.RuleT_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'
 | T_Clo c cv g top e l r r' : JitEmitRuleClo.RuleT_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'
 | T_App c cv g top e l r r' : JitEmitRuleApp.RuleT_App Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'
 | T_Trap c cv g top e l r r' : JitEmitRuleTrap.RuleT_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> CompT c cv g top e l r r'

(* An operand: a variable's own slot, a constant, or the next free slot after computing it. *)
with CompOp : B.code -> list name -> env -> N -> expr -> B.operand -> N -> list B.instr -> list B.instr -> Prop :=
 | O_var c cv g top x s r : lookup x g = Some s -> s < top -> CompOp c cv g top (EVar x) (B.OSlot s) top r r
 | O_lit c cv g top e v v' k r : lit_val e = Some v -> konst c k = Some v' -> VR v v' ->
     CompOp c cv g top e (B.OConst k) top r r
 | O_val c cv g top e r r' : Comp c cv g (top + 1) e (DSlot top) r r' ->
     CompOp c cv g top e (B.OSlot top) (top + 1) r r'
 | O_type c cv g top e o top2 r r' : CompOp c cv g top e o top2 r r' -> CompOp c cv g top (EType e) o top2 r r'
 | O_Eq c cv g top e o top2 r r' : JitEmitRuleEq.RuleO_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'
 | O_Store c cv g top e o top2 r r' : JitEmitRuleStore.RuleO_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'
 | O_Prim c cv g top e o top2 r r' : JitEmitRulePrim.RuleO_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'
 | O_DoFold c cv g top e o top2 r r' : JitEmitRuleDoFold.RuleO_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'
 | O_Clo c cv g top e o top2 r r' : JitEmitRuleClo.RuleO_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'
 | O_App c cv g top e o top2 r r' : JitEmitRuleApp.RuleO_App Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'
 | O_Trap c cv g top e o top2 r r' : JitEmitRuleTrap.RuleO_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> CompOp c cv g top e o top2 r r'

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



(* ---------- the nested mutual induction principle ---------- *)
Section Ind.
Variables (PC : B.code -> list name -> env -> N -> expr -> dest -> list B.instr -> list B.instr -> Prop)
 (PT : B.code -> list name -> env -> N -> expr -> N -> list B.instr -> list B.instr -> Prop)
 (PO : B.code -> list name -> env -> N -> expr -> B.operand -> N -> list B.instr -> list B.instr -> Prop)
 (PS : B.code -> list name -> env -> N -> list expr -> list B.operand -> list B.instr -> list B.instr -> Prop)
 (PW : B.code -> list name -> env -> N -> list expr -> list B.instr -> list B.instr -> Prop)
 (PA : B.code -> list name -> env -> N -> N -> list expr -> list (N * N) -> list B.instr -> list B.instr -> Prop).
(* One case per constructor: its premises, each recursive one followed by its motive. A family
   hook's case gets the rule derivation and the same derivation over the IH-carrying relations
   (Rule_X_All Comp PC ...), so each nested sub-derivation comes with its motive. *)
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
Hypothesis h_C_Eq : forall c cv g top e d r r', JitEmitRuleEq.Rule_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> JitEmitRuleEq.Rule_Eq_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_C_Store : forall c cv g top e d r r', JitEmitRuleStore.Rule_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> JitEmitRuleStore.Rule_Store_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_C_Prim : forall c cv g top e d r r', JitEmitRulePrim.Rule_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> JitEmitRulePrim.Rule_Prim_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_C_DoFold : forall c cv g top e d r r', JitEmitRuleDoFold.Rule_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> JitEmitRuleDoFold.Rule_DoFold_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_C_Clo : forall c cv g top e d r r', JitEmitRuleClo.Rule_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> JitEmitRuleClo.Rule_Clo_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_C_App : forall c cv g top e d r r', JitEmitRuleApp.Rule_App Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> JitEmitRuleApp.Rule_App_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_C_Trap : forall c cv g top e d r r', JitEmitRuleTrap.Rule_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e d r r' -> JitEmitRuleTrap.Rule_Trap_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e d r r' -> PC c cv g top e d r r'.
Hypothesis h_T_leaf : forall c cv g top e o top2 l r r', CompOp c cv g top e o top2 r (B.IJumpIfFalse o l :: r') -> PO c cv g top e o top2 r (B.IJumpIfFalse o l :: r') -> PT c cv g top e l r r'.
Hypothesis h_T_and : forall c cv g top x y l r r1 r', CompT c cv g top x l r r1 -> PT c cv g top x l r r1 -> CompT c cv g top y l r1 r' -> PT c cv g top y l r1 r' -> PT c cv g top (EAnd x y) l r r'.
Hypothesis h_T_or : forall c cv g top x y l nx th r r2 r', CompT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) -> PT c cv g top x nx r (B.IJump th :: B.ILabel nx :: r2) -> lbl c nx = Some r2 -> CompT c cv g top y l r2 (B.ILabel th :: r') -> PT c cv g top y l r2 (B.ILabel th :: r') -> lbl c th = Some r' -> PT c cv g top (EOr x y) l r r'.
Hypothesis h_T_let : forall c cv g top x a b l r r1 r', Comp c cv g (top + 1) a (DSlot top) r r1 -> PC c cv g (top + 1) a (DSlot top) r r1 -> CompT c cv ((x, top) :: g) (top + 1) b l r1 r' -> PT c cv ((x, top) :: g) (top + 1) b l r1 r' -> PT c cv g top (ELet x a b) l r r'.
Hypothesis h_T_alias : forall c cv g top x y s b l r r', lookup y g = Some s -> CompT c cv ((x, s) :: g) top b l r r' -> PT c cv ((x, s) :: g) top b l r r' -> PT c cv g top (ELet x (EVar y) b) l r r'.
Hypothesis h_T_type : forall c cv g top e l r r', CompT c cv g top e l r r' -> PT c cv g top e l r r' -> PT c cv g top (EType e) l r r'.
Hypothesis h_T_Eq : forall c cv g top e l r r', JitEmitRuleEq.RuleT_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> JitEmitRuleEq.RuleT_Eq_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e l r r' -> PT c cv g top e l r r'.
Hypothesis h_T_Store : forall c cv g top e l r r', JitEmitRuleStore.RuleT_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> JitEmitRuleStore.RuleT_Store_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e l r r' -> PT c cv g top e l r r'.
Hypothesis h_T_Prim : forall c cv g top e l r r', JitEmitRulePrim.RuleT_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> JitEmitRulePrim.RuleT_Prim_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e l r r' -> PT c cv g top e l r r'.
Hypothesis h_T_DoFold : forall c cv g top e l r r', JitEmitRuleDoFold.RuleT_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> JitEmitRuleDoFold.RuleT_DoFold_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e l r r' -> PT c cv g top e l r r'.
Hypothesis h_T_Clo : forall c cv g top e l r r', JitEmitRuleClo.RuleT_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> JitEmitRuleClo.RuleT_Clo_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e l r r' -> PT c cv g top e l r r'.
Hypothesis h_T_App : forall c cv g top e l r r', JitEmitRuleApp.RuleT_App Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> JitEmitRuleApp.RuleT_App_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e l r r' -> PT c cv g top e l r r'.
Hypothesis h_T_Trap : forall c cv g top e l r r', JitEmitRuleTrap.RuleT_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e l r r' -> JitEmitRuleTrap.RuleT_Trap_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e l r r' -> PT c cv g top e l r r'.
Hypothesis h_O_var : forall c cv g top x s r, lookup x g = Some s -> s < top -> PO c cv g top (EVar x) (B.OSlot s) top r r.
Hypothesis h_O_lit : forall c cv g top e v v' k r, lit_val e = Some v -> konst c k = Some v' -> VR v v' -> PO c cv g top e (B.OConst k) top r r.
Hypothesis h_O_val : forall c cv g top e r r', Comp c cv g (top + 1) e (DSlot top) r r' -> PC c cv g (top + 1) e (DSlot top) r r' -> PO c cv g top e (B.OSlot top) (top + 1) r r'.
Hypothesis h_O_type : forall c cv g top e o top2 r r', CompOp c cv g top e o top2 r r' -> PO c cv g top e o top2 r r' -> PO c cv g top (EType e) o top2 r r'.
Hypothesis h_O_Eq : forall c cv g top e o top2 r r', JitEmitRuleEq.RuleO_Eq Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> JitEmitRuleEq.RuleO_Eq_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e o top2 r r' -> PO c cv g top e o top2 r r'.
Hypothesis h_O_Store : forall c cv g top e o top2 r r', JitEmitRuleStore.RuleO_Store Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> JitEmitRuleStore.RuleO_Store_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e o top2 r r' -> PO c cv g top e o top2 r r'.
Hypothesis h_O_Prim : forall c cv g top e o top2 r r', JitEmitRulePrim.RuleO_Prim Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> JitEmitRulePrim.RuleO_Prim_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e o top2 r r' -> PO c cv g top e o top2 r r'.
Hypothesis h_O_DoFold : forall c cv g top e o top2 r r', JitEmitRuleDoFold.RuleO_DoFold Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> JitEmitRuleDoFold.RuleO_DoFold_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e o top2 r r' -> PO c cv g top e o top2 r r'.
Hypothesis h_O_Clo : forall c cv g top e o top2 r r', JitEmitRuleClo.RuleO_Clo Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> JitEmitRuleClo.RuleO_Clo_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e o top2 r r' -> PO c cv g top e o top2 r r'.
Hypothesis h_O_App : forall c cv g top e o top2 r r', JitEmitRuleApp.RuleO_App Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> JitEmitRuleApp.RuleO_App_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e o top2 r r' -> PO c cv g top e o top2 r r'.
Hypothesis h_O_Trap : forall c cv g top e o top2 r r', JitEmitRuleTrap.RuleO_Trap Comp CompT CompOp CompOps CompW CompTA c cv g top e o top2 r r' -> JitEmitRuleTrap.RuleO_Trap_All Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA c cv g top e o top2 r r' -> PO c cv g top e o top2 r r'.
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
 | C_Eq c cv g top e d r r' H0 => h_C_Eq c cv g top e d r r' H0 (JitEmitRuleEq.Rule_Eq_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 | C_Store c cv g top e d r r' H0 => h_C_Store c cv g top e d r r' H0 (JitEmitRuleStore.Rule_Store_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 | C_Prim c cv g top e d r r' H0 => h_C_Prim c cv g top e d r r' H0 (JitEmitRulePrim.Rule_Prim_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 | C_DoFold c cv g top e d r r' H0 => h_C_DoFold c cv g top e d r r' H0 (JitEmitRuleDoFold.Rule_DoFold_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 | C_Clo c cv g top e d r r' H0 => h_C_Clo c cv g top e d r r' H0 (JitEmitRuleClo.Rule_Clo_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 | C_App c cv g top e d r r' H0 => h_C_App c cv g top e d r r' H0 (JitEmitRuleApp.Rule_App_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 | C_Trap c cv g top e d r r' H0 => h_C_Trap c cv g top e d r r' H0 (JitEmitRuleTrap.Rule_Trap_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e d r r' H0)
 end
with CompT_ind' c cv g top e l r r' (H : CompT c cv g top e l r r') {struct H} : PT c cv g top e l r r' :=
 match H with
 | T_leaf c cv g top e o top2 l r r' H0 => h_T_leaf c cv g top e o top2 l r r' H0 (CompOp_ind' _ _ _ _ _ _ _ _ _ H0)
 | T_and c cv g top x y l r r1 r' H0 H1 => h_T_and c cv g top x y l r r1 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 (CompT_ind' _ _ _ _ _ _ _ _ H1)
 | T_or c cv g top x y l nx th r r2 r' H0 H1 H2 H3 => h_T_or c cv g top x y l nx th r r2 r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0) H1 H2 (CompT_ind' _ _ _ _ _ _ _ _ H2) H3
 | T_let c cv g top x a b l r r1 r' H0 H1 => h_T_let c cv g top x a b l r r1 r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0) H1 (CompT_ind' _ _ _ _ _ _ _ _ H1)
 | T_alias c cv g top x y s b l r r' H0 H1 => h_T_alias c cv g top x y s b l r r' H0 H1 (CompT_ind' _ _ _ _ _ _ _ _ H1)
 | T_type c cv g top e l r r' H0 => h_T_type c cv g top e l r r' H0 (CompT_ind' _ _ _ _ _ _ _ _ H0)
 | T_Eq c cv g top e l r r' H0 => h_T_Eq c cv g top e l r r' H0 (JitEmitRuleEq.RuleT_Eq_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e l r r' H0)
 | T_Store c cv g top e l r r' H0 => h_T_Store c cv g top e l r r' H0 (JitEmitRuleStore.RuleT_Store_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e l r r' H0)
 | T_Prim c cv g top e l r r' H0 => h_T_Prim c cv g top e l r r' H0 (JitEmitRulePrim.RuleT_Prim_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e l r r' H0)
 | T_DoFold c cv g top e l r r' H0 => h_T_DoFold c cv g top e l r r' H0 (JitEmitRuleDoFold.RuleT_DoFold_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e l r r' H0)
 | T_Clo c cv g top e l r r' H0 => h_T_Clo c cv g top e l r r' H0 (JitEmitRuleClo.RuleT_Clo_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e l r r' H0)
 | T_App c cv g top e l r r' H0 => h_T_App c cv g top e l r r' H0 (JitEmitRuleApp.RuleT_App_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e l r r' H0)
 | T_Trap c cv g top e l r r' H0 => h_T_Trap c cv g top e l r r' H0 (JitEmitRuleTrap.RuleT_Trap_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e l r r' H0)
 end
with CompOp_ind' c cv g top e o top2 r r' (H : CompOp c cv g top e o top2 r r') {struct H} : PO c cv g top e o top2 r r' :=
 match H with
 | O_var c cv g top x s r H0 H1 => h_O_var c cv g top x s r H0 H1
 | O_lit c cv g top e v v' k r H0 H1 H2 => h_O_lit c cv g top e v v' k r H0 H1 H2
 | O_val c cv g top e r r' H0 => h_O_val c cv g top e r r' H0 (Comp_ind' _ _ _ _ _ _ _ _ H0)
 | O_type c cv g top e o top2 r r' H0 => h_O_type c cv g top e o top2 r r' H0 (CompOp_ind' _ _ _ _ _ _ _ _ _ H0)
 | O_Eq c cv g top e o top2 r r' H0 => h_O_Eq c cv g top e o top2 r r' H0 (JitEmitRuleEq.RuleO_Eq_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e o top2 r r' H0)
 | O_Store c cv g top e o top2 r r' H0 => h_O_Store c cv g top e o top2 r r' H0 (JitEmitRuleStore.RuleO_Store_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e o top2 r r' H0)
 | O_Prim c cv g top e o top2 r r' H0 => h_O_Prim c cv g top e o top2 r r' H0 (JitEmitRulePrim.RuleO_Prim_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e o top2 r r' H0)
 | O_DoFold c cv g top e o top2 r r' H0 => h_O_DoFold c cv g top e o top2 r r' H0 (JitEmitRuleDoFold.RuleO_DoFold_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e o top2 r r' H0)
 | O_Clo c cv g top e o top2 r r' H0 => h_O_Clo c cv g top e o top2 r r' H0 (JitEmitRuleClo.RuleO_Clo_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e o top2 r r' H0)
 | O_App c cv g top e o top2 r r' H0 => h_O_App c cv g top e o top2 r r' H0 (JitEmitRuleApp.RuleO_App_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e o top2 r r' H0)
 | O_Trap c cv g top e o top2 r r' H0 => h_O_Trap c cv g top e o top2 r r' H0 (JitEmitRuleTrap.RuleO_Trap_all Comp PC CompT PT CompOp PO CompOps PS CompW PW CompTA PA Comp_ind' CompT_ind' CompOp_ind' CompOps_ind' CompW_ind' CompTA_ind' c cv g top e o top2 r r' H0)
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

(* ---------- JitLowerRel's derivations embed ---------- *)
Scheme oComp_m := Minimality for JitLowerRel.Comp Sort Prop
 with oCompT_m := Minimality for JitLowerRel.CompT Sort Prop
 with oCompOp_m := Minimality for JitLowerRel.CompOp Sort Prop
 with oCompOps_m := Minimality for JitLowerRel.CompOps Sort Prop
 with oCompW_m := Minimality for JitLowerRel.CompW Sort Prop
 with oCompTA_m := Minimality for JitLowerRel.CompTA Sort Prop.
Combined Scheme oComp_mut from oComp_m, oCompT_m, oCompOp_m, oCompOps_m, oCompW_m, oCompTA_m.

(* Every derivation of JitLowerRel's relations at code c is one of these at (c, cv), for any cv:
   no copied constructor reads cv, and none uses a hook. *)
Theorem comp_embed : forall c,
 (forall g top e d r r', JitLowerRel.Comp c g top e d r r' -> forall cv, Comp c cv g top e d r r') /\
 (forall g top e l r r', JitLowerRel.CompT c g top e l r r' -> forall cv, CompT c cv g top e l r r') /\
 (forall g top e o top2 r r', JitLowerRel.CompOp c g top e o top2 r r' -> forall cv, CompOp c cv g top e o top2 r r') /\
 (forall g top es os r r', JitLowerRel.CompOps c g top es os r r' -> forall cv, CompOps c cv g top es os r r') /\
 (forall g s es r r', JitLowerRel.CompW c g s es r r' -> forall cv, CompW c cv g s es r r') /\
 (forall g s t es ms r r', JitLowerRel.CompTA c g s t es ms r r' -> forall cv, CompTA c cv g s t es ms r r').
Proof.
 intro c. apply (oComp_mut c); intros;
  [ eapply C_lit | eapply C_move | eapply C_same | eapply C_prim | eapply C_let | eapply C_alias
  | eapply C_if_slot | eapply C_if_ret | eapply C_cond_nil | eapply C_cond_true | eapply C_cond_slot
  | eapply C_cond_ret | eapply C_type | eapply C_and | eapply C_or | eapply C_ret | eapply C_call
  | eapply C_tail | eapply C_chain
  | eapply T_leaf | eapply T_and | eapply T_or | eapply T_let | eapply T_alias | eapply T_type
  | eapply O_var | eapply O_lit | eapply O_val | eapply O_type
  | eapply Os_nil | eapply Os_cons | eapply W_nil | eapply W_cons
  | eapply TA_nil | eapply TA_same | eapply TA_temp | eapply TA_direct ]; eauto.
Qed.

Corollary comp_embed_fn : forall c ps b, JitLowerRel.CompFn c ps b ->
 exists r', Comp c [] (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c) r'.
Proof. intros c ps b [r' H]. exists r'. apply (proj1 (comp_embed c)); exact H. Qed.

(* ---------- code objects ---------- *)
(* A top-level function's code: its body with the parameters in slots 2 up, nothing captured. *)
Definition CompFn' (c : B.code) (ps : list name) (b : expr) : Prop :=
 exists r', Comp c [] (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c) r'.

(* A closure's code object nc for parameters ps (one for a lambda, none for a freeze) and body b:
   the arity, no multi-argument entry, and the body lowered with the parameters in slots 2 up and
   the variables cv read from the closure's captures.
   Does NOT say: anything about lambda chains with an (entry N L) prefix (finish-entry). Stage 0
   has none (lower.shen: code lowered with Sealed non-empty has none); a closure with an entry is
   not related by JitEmitInv.VRh. *)
Definition CloOK (nc : B.code) (cv : list name) (ps : list name) (b : expr) : Prop :=
 B.code_arity nc = N.of_nat (List.length ps) /\ B.code_entry nc = None /\
 exists r', Comp nc cv (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins nc) r'.
End JitEmitRel.
