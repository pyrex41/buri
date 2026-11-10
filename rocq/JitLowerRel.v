(* Shen/JIT Phase 2: what it means for bytecode to be a lowering of a KLambda expression.
   `Comp` and its companions relate a resolved expression to the instructions of one code object,
   following the shapes of src/lowerer/lower.shen (934cfa5; these shapes are unchanged since d3348ce). They say nothing about how those
   instructions were produced, so a theorem over them holds for any code they accept, whatever
   lowered it. JitLowerSim.v proves preservation over them; JitLowerCheck.v decides them on
   captured output. Inlining, sharing, closures, handlers, defun and eval-kl are not here: the
   ledger lists each one, under OB-JIT-LOWER. *)
From Coq Require Import List ZArith NArith PArith Bool String.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitProfile.
Import ListNotations.
Module JitLowerRel.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* ---------- data ---------- *)
Inductive VR : value -> B.val -> Prop :=
 | VR_int z : VR (VNum (NInt z)) (B.VFix z)
 | VR_real b : VR (VNum (NFloat b)) (B.VReal b)
 | VR_sym s : VR (VSym s) (B.VSym (B.sym_of_text s))
 | VR_bool b : VR (VBool b) (B.VBool b)
 | VR_str t : VR (VStr t) (B.VStr t)
 | VR_nil : VR VNil B.VNil
 | VR_cons a a' d d' : VR a a' -> VR d d' -> VR (VCons a d) (B.VPair a' d').

(* The literals, and the constants they are. *)
Definition lit_val (e : expr) : option value := match e with
 | ENum n => Some (VNum n) | EStr t => Some (VStr t) | ESym s => Some (VSym s)
 | EBool b => Some (VBool b) | ENil => Some VNil | _ => None end.

(* The primitives this level admits, and what each is in the bytecode. *)
Definition pmap (p : prim) : option B.prim := match p with
 | PAdd => Some B.PAdd | PSub => Some B.PSub | PMul => Some B.PMul
 | PGt => Some B.PGt | PLt => Some B.PLt | PGe => Some B.PGe | PLe => Some B.PLe
 | PCons => Some B.PCons | PHd => Some B.PHd | PTl => Some B.PTl | PConsP => Some B.PConsp
 | PNumberP => Some B.PNumberp | PStringP => Some B.PStringp | PEqual => Some B.PEq
 | _ => None end.

Definition prim_of_name (f : name) : option prim :=
 find (fun p => text_eqb f (of_string (prim_name p))) all_prims.

Definition env := list (name * N).

(* The variables whose slot is S are dead once S is written: their entries go, including any
   entry they shadow, so no later lookup can reach an older binding of the name. *)
Definition slot_is (o : option N) (s : N) : bool := match o with Some x => N.eqb x s | None => false end.
Definition kill (s : N) (e : env) : env :=
 filter (fun p => negb (slot_is (lookup (fst p) e) s)) e.

Fixpoint bind (ps : list name) (s : N) : env := match ps with
 | [] => [] | p :: ps => (p, s) :: bind ps (s + 1) end.

Inductive dest := DSlot (d : N) | DRet.
Definition call_instr (i : B.instr) (d a : N) (f : positive) (n : N) : Prop :=
 i = B.ICall d a f n \/ i = B.ICallSealed d a f n.
Definition tail_instr (i : B.instr) (a : N) (f : positive) (n : N) : Prop :=
 i = B.ITail a f n \/ i = B.ITailSealed a f n.
Definition not_prim_name (f : name) : Prop := prim_of_name f = None.

Section Code.
Variable c : B.code.
Definition ins := B.code_ins c.
Definition konst (k : N) := nth_error (B.code_consts c) (N.to_nat k).
Definition lbl (l : N) := B.find_label l ins.

(* = is admitted only with a constant operand it cannot misjudge: a fixnum, string, symbol,
   boolean, (), or a real that is not a NaN. On two NaNs the model is stuck (RIdentity,
   OB-JIT-NAN-IDENTITY) where the source answers false; an atom of these kinds never meets that.
   Symbols compare by name, as B.sym_of_text is injective (OB-JIT-SYM-INJECTIVE). *)
Definition eq_safe_val (w : B.val) : bool := match w with
 | B.VFix _ | B.VStr _ | B.VSym _ | B.VBool _ | B.VNil => true
 | B.VReal b => negb (JitFloat.JitFloat.is_nan b)
 | _ => false end.
Definition eq_safe_op (o : B.operand) : bool := match o with
 | B.OConst k => match konst k with Some w => eq_safe_val w | None => false end
 | B.OSlot _ => false end.
Definition pguard (q : B.prim) (ops : list B.operand) : bool := match q with
 | B.PEq => existsb eq_safe_op ops | _ => true end.

(* `Comp e top e dst r r'`: r starts with e's code, then r'. A value goes to slot d, or is
   returned. Every slot e's code writes is at or above top, or is d, and d last. *)
Inductive Comp : env -> N -> expr -> dest -> list B.instr -> list B.instr -> Prop :=
 | C_lit g top e v v' d k r : lit_val e = Some v -> konst k = Some v' -> VR v v' ->
     Comp g top e (DSlot d) (B.IConst d k :: r) r
 | C_move g top x s d r : lookup x g = Some s -> s <> d ->
     Comp g top (EVar x) (DSlot d) (B.IMove d s :: r) r
 | C_same g top x d r : lookup x g = Some d -> Comp g top (EVar x) (DSlot d) r r
 | C_prim g top f p q args ops d r r' :
     prim_of_name f = Some p -> pmap p = Some q -> List.length args = prim_arity p -> args <> [] ->
     CompOps g top args ops r (B.IPrim d q ops :: r') -> pguard q ops = true ->
     Comp g top (ECall f args) (DSlot d) r r'
 | C_let g top x a b dst r r1 r' : Comp g (top + 1) a (DSlot top) r r1 ->
     Comp ((x, top) :: g) (top + 1) b dst r1 r' -> Comp g top (ELet x a b) dst r r'
 | C_alias g top x y s b dst r r' : lookup y g = Some s ->
     Comp ((x, s) :: g) top b dst r r' -> Comp g top (ELet x (EVar y) b) dst r r'
 | C_if_slot g top t a b d l e0 r r1 r3 r' : CompT g top t l r r1 ->
     Comp g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> lbl l = Some r3 ->
     Comp g top b (DSlot d) r3 (B.ILabel e0 :: r') -> lbl e0 = Some r' ->
     Comp g top (EIf t a b) (DSlot d) r r'
 | C_if_ret g top t a b l r r1 r3 r' : CompT g top t l r r1 ->
     Comp g top a DRet r1 (B.ILabel l :: r3) -> lbl l = Some r3 -> Comp g top b DRet r3 r' ->
     Comp g top (EIf t a b) DRet r r'
 | C_cond_nil g top d r : Comp g top (ECond []) (DSlot d) (B.IPrim d B.PRaiseCond [] :: r) r
 | C_cond_true g top x rest dst r r' : Comp g top x dst r r' ->
     Comp g top (ECond ((EBool true, x) :: rest)) dst r r'
 | C_cond_slot g top t a rest d l e0 r r1 r3 r' : CompT g top t l r r1 ->
     Comp g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> lbl l = Some r3 ->
     Comp g top (ECond rest) (DSlot d) r3 (B.ILabel e0 :: r') -> lbl e0 = Some r' ->
     Comp g top (ECond ((t, a) :: rest)) (DSlot d) r r'
 | C_cond_ret g top t a rest l r r1 r3 r' : CompT g top t l r r1 ->
     Comp g top a DRet r1 (B.ILabel l :: r3) -> lbl l = Some r3 -> Comp g top (ECond rest) DRet r3 r' ->
     Comp g top (ECond ((t, a) :: rest)) DRet r r'
 | C_type g top e dst r r' : Comp g top e dst r r' -> Comp g top (EType e) dst r r'
 | C_and g top x y d l e0 kt kf r r1 r' : CompT g top x l r r1 ->
     CompT g top y l r1 (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
     konst kt = Some (B.VBool true) -> konst kf = Some (B.VBool false) ->
     lbl l = Some (B.IConst d kf :: B.ILabel e0 :: r') -> lbl e0 = Some r' ->
     Comp g top (EAnd x y) (DSlot d) r r'
 | C_or g top x y d l nx th e0 kt kf r r2 r' : CompT g top x nx r (B.IJump th :: B.ILabel nx :: r2) ->
     lbl nx = Some r2 ->
     CompT g top y l r2 (B.ILabel th :: B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
     lbl th = Some (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
     konst kt = Some (B.VBool true) -> konst kf = Some (B.VBool false) ->
     lbl l = Some (B.IConst d kf :: B.ILabel e0 :: r') -> lbl e0 = Some r' ->
     Comp g top (EOr x y) (DSlot d) r r'
 | C_ret g top e o top2 r r' : CompOp g top e o top2 r (B.IReturn o :: r') -> Comp g top e DRet r r'
 | C_call g top f args d n i r r' : not_prim_name f -> n = N.of_nat (List.length args) ->
     CompW g (top + 2) args r (i :: r') -> call_instr i d top (B.sym_of_text f) n ->
     Comp g top (ECall f args) (DSlot d) r r'
 | C_tail g top f args n t i r r' : not_prim_name f -> n = N.of_nat (List.length args) ->
     n + 2 <= t -> top <= t -> CompTA g 2 t args [] r (i :: r') ->
     tail_instr i 0 (B.sym_of_text f) n ->
     Comp g top (ECall f args) DRet r r'
 (* A cons with a constant head, in place (lower.shen's value-h, from d3348ce): the tail goes to
    d, and the cons reads it there and writes d again. lower.shen takes this only when d is not a
    parameter slot, which check.shen asks of it; the simulation doesn't need that. *)
 | C_chain g top f a e v v' k d r r' : prim_of_name f = Some PCons ->
     lit_val a = Some v -> konst k = Some v' -> VR v v' ->
     Comp g top e (DSlot d) r (B.IPrim d B.PCons [B.OConst k; B.OSlot d] :: r') ->
     Comp g top (ECall f [a; e]) (DSlot d) r r'

(* Falls through when the value is true, and goes to l when it is false. *)
with CompT : env -> N -> expr -> N -> list B.instr -> list B.instr -> Prop :=
 | T_leaf g top e o top2 l r r' : CompOp g top e o top2 r (B.IJumpIfFalse o l :: r') -> CompT g top e l r r'
 | T_and g top x y l r r1 r' : CompT g top x l r r1 -> CompT g top y l r1 r' -> CompT g top (EAnd x y) l r r'
 | T_or g top x y l nx th r r2 r' : CompT g top x nx r (B.IJump th :: B.ILabel nx :: r2) ->
     lbl nx = Some r2 -> CompT g top y l r2 (B.ILabel th :: r') -> lbl th = Some r' ->
     CompT g top (EOr x y) l r r'
 | T_let g top x a b l r r1 r' : Comp g (top + 1) a (DSlot top) r r1 ->
     CompT ((x, top) :: g) (top + 1) b l r1 r' -> CompT g top (ELet x a b) l r r'
 | T_alias g top x y s b l r r' : lookup y g = Some s ->
     CompT ((x, s) :: g) top b l r r' -> CompT g top (ELet x (EVar y) b) l r r'
 | T_type g top e l r r' : CompT g top e l r r' -> CompT g top (EType e) l r r'

(* An operand: a variable's own slot, a constant, or the next free slot after computing it. *)
with CompOp : env -> N -> expr -> B.operand -> N -> list B.instr -> list B.instr -> Prop :=
 | O_var g top x s r : lookup x g = Some s -> s < top -> CompOp g top (EVar x) (B.OSlot s) top r r
 | O_lit g top e v v' k r : lit_val e = Some v -> konst k = Some v' -> VR v v' ->
     CompOp g top e (B.OConst k) top r r
 | O_val g top e r r' : Comp g (top + 1) e (DSlot top) r r' ->
     CompOp g top e (B.OSlot top) (top + 1) r r'
 | O_type g top e o top2 r r' : CompOp g top e o top2 r r' -> CompOp g top (EType e) o top2 r r'

with CompOps : env -> N -> list expr -> list B.operand -> list B.instr -> list B.instr -> Prop :=
 | Os_nil g top r : CompOps g top [] [] r r
 | Os_cons g top e es o os top2 r r1 r' : CompOp g top e o top2 r r1 ->
     CompOps g top2 es os r1 r' -> CompOps g top (e :: es) (o :: os) r r'

(* Arguments in consecutive slots from S: a call window. *)
with CompW : env -> N -> list expr -> list B.instr -> list B.instr -> Prop :=
 | W_nil g s r : CompW g s [] r r
 | W_cons g s e es r r1 r' : Comp g (s + 1) e (DSlot s) r r1 -> CompW g (s + 1) es r1 r' ->
     CompW g s (e :: es) r r'

(* A named tail call's arguments, each for parameter slot S: one already there, one computed
   into a temporary and moved last because a later argument reads S, or one computed in place,
   after which S's variables are dead. The moves are newest first, as the code emits them. *)
with CompTA : env -> N -> N -> list expr -> list (N * N) -> list B.instr -> list B.instr -> Prop :=
 | TA_nil g s t ms r' : CompTA g s t [] ms (map (fun m => B.IMove (fst m) (snd m)) ms ++ r') r'
 | TA_same g s t x es ms r r' : lookup x g = Some s -> CompTA g (s + 1) t es ms r r' ->
     CompTA g s t (EVar x :: es) ms r r'
 | TA_temp g s t e es ms r r1 r' : Comp g (t + 1) e (DSlot t) r r1 ->
     CompTA g (s + 1) (t + 1) es ((s, t) :: ms) r1 r' -> CompTA g s t (e :: es) ms r r'
 | TA_direct g s t e es ms r r1 r' : Comp g t e (DSlot s) r r1 ->
     CompTA (kill s g) (s + 1) t es ms r1 r' -> CompTA g s t (e :: es) ms r r'.
End Code.

(* A function's code: its body lowered with the parameters in slots 2 up. *)
Definition CompFn (c : B.code) (ps : list name) (b : expr) : Prop :=
 exists r', Comp c (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c) r'.
End JitLowerRel.
