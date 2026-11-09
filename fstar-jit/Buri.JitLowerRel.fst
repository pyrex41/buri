(* Port of rocq/JitLowerRel.v: what it means for bytecode to be a lowering of a KLambda expression.
   Encoding: Rocq's mutual inductive Props Comp/CompT/CompOp/CompOps/CompW/CompTA are mutual
   inductive F* types (proof-relevant, `noeq`), with the Section variable `c` as a parameter.
   Propositional premises (equalities, disequalities, `call_instr`, `<=`) are `squash` fields. *)
module Buri.JitLowerRel
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
module B = Buri.JitBytecode

(* ---------- data ---------- *)
noeq type vr : value -> B.val_ -> Type0 =
  | VR_int : z:int -> vr (VNum (NInt z)) (B.VFix z)
  | VR_real : b:nat -> vr (VNum (NFloat b)) (B.VReal b)
  | VR_sym : s:name -> vr (VSym s) (B.VSym (B.sym_of_text s))
  | VR_bool : b:bool -> vr (VBool b) (B.VBool b)
  | VR_str : t:text -> vr (VStr t) (B.VStr t)
  | VR_nil : vr VNil B.VNil
  | VR_cons : a:value -> a':B.val_ -> d:value -> d':B.val_ -> vr a a' -> vr d d' -> vr (VCons a d) (B.VPair a' d')

(* VR as a proposition, for use inside quantified statements (MEnv). Z3 did not instantiate
   quantifiers whose body held `inhabited (vr v v')` (an existential over a type indexed by the
   bound values); `vrp` says the same (vrp_iff) and avoids that. *)
let rec vrp (v : value) (w : B.val_) : Tot prop (decreases v) = match v, w with
  | VNum (NInt z), B.VFix y -> z == y
  | VNum (NFloat b), B.VReal c -> b == c
  | VSym s, B.VSym p -> p == B.sym_of_text s
  | VBool b, B.VBool c -> b == c
  | VStr t, B.VStr u -> t == u
  | VNil, B.VNil -> True
  | VCons a d, B.VPair a' d' -> vrp a a' /\ vrp d d'
  | _, _ -> False
let rec vrp_of_vr (#v : value) (#w : B.val_) (d : vr v w) : Lemma (ensures vrp v w) (decreases d) =
  match d with
  | VR_cons a a' d1 d' h1 h2 -> vrp_of_vr h1; vrp_of_vr h2
  | _ -> ()
let rec vr_of_vrp (v : value) (w : B.val_) : Pure (vr v w) (requires vrp v w) (ensures fun _ -> True) (decreases v) =
  match v, w with
  | VNum (NInt z), B.VFix y -> VR_int z
  | VNum (NFloat b), B.VReal c -> VR_real b
  | VSym s, B.VSym p -> VR_sym s
  | VBool b, B.VBool c -> VR_bool b
  | VStr t, B.VStr u -> VR_str t
  | VNil, B.VNil -> VR_nil
  | VCons a d, B.VPair a' d' -> VR_cons a a' d d' (vr_of_vrp a a') (vr_of_vrp d d')

let lit_val (e : expr) : option value = match e with
  | ENum n -> Some (VNum n) | EStr t -> Some (VStr t) | ESym s -> Some (VSym s)
  | EBool b -> Some (VBool b) | ENil -> Some VNil | _ -> None

let pmap (p : prim) : option B.prim = match p with
  | PAdd -> Some B.PAdd | PSub -> Some B.PSub | PMul -> Some B.PMul
  | PGt -> Some B.PGt | PLt -> Some B.PLt | PGe -> Some B.PGe | PLe -> Some B.PLe
  | PCons -> Some B.PCons | PHd -> Some B.PHd | PTl -> Some B.PTl | PConsP -> Some B.PConsp
  | PNumberP -> Some B.PNumberp | PStringP -> Some B.PStringp
  | _ -> None

let prim_of_name (f : name) : option prim =
  find (fun p -> text_eqb f (of_string (prim_name p))) all_prims

type env = list (name & nat)

let slot_is (o : option nat) (s : nat) : bool = match o with Some x -> x = s | None -> false
let kill (s : nat) (e : env) : env =
  filter (fun (p : name & nat) -> not (slot_is (lookup (fst p) e) s)) e

let rec bind (ps : list name) (s : nat) : env = match ps with
  | [] -> [] | p :: ps -> (p, s) :: bind ps (s + 1)

type dest = | DSlot : d:nat -> dest | DRet
let call_instr (i : B.instr) (d a : nat) (f : pos) (n : nat) : prop =
  i == B.ICall d a f n \/ i == B.ICallSealed d a f n
let tail_instr (i : B.instr) (a : nat) (f : pos) (n : nat) : prop =
  i == B.ITail a f n \/ i == B.ITailSealed a f n
let not_prim_name (f : name) : prop = prim_of_name f == None

let ins (c : B.code) = B.code_ins c
let konst (c : B.code) (k : nat) = nth_error (B.code_consts c) k
let lbl (c : B.code) (l : nat) = B.find_label l (ins c)

let moves (ms : list (nat & nat)) : list B.instr = map (fun (m : nat & nat) -> B.IMove (fst m) (snd m)) ms

noeq type comp (c : B.code) : env -> nat -> expr -> dest -> list B.instr -> list B.instr -> Type0 =
  | C_lit : g:env -> top:nat -> e:expr -> v:value -> v':B.val_ -> d:nat -> k:nat -> r:list B.instr ->
      squash (lit_val e == Some v) -> squash (konst c k == Some v') -> vr v v' ->
      comp c g top e (DSlot d) (B.IConst d k :: r) r
  | C_move : g:env -> top:nat -> x:name -> s:nat -> d:nat -> r:list B.instr ->
      squash (lookup x g == Some s) -> squash (s <> d) ->
      comp c g top (EVar x) (DSlot d) (B.IMove d s :: r) r
  | C_same : g:env -> top:nat -> x:name -> d:nat -> r:list B.instr ->
      squash (lookup x g == Some d) -> comp c g top (EVar x) (DSlot d) r r
  | C_prim : g:env -> top:nat -> f:name -> p:prim -> q:B.prim -> args:list expr -> ops:list B.operand ->
      d:nat -> r:list B.instr -> r':list B.instr ->
      squash (prim_of_name f == Some p) -> squash (pmap p == Some q) -> squash (length args = prim_arity p) ->
      squash (~(args == [])) ->
      compOps c g top args ops r (B.IPrim d q ops :: r') -> comp c g top (ECall f args) (DSlot d) r r'
  | C_let : g:env -> top:nat -> x:name -> a:expr -> b:expr -> dst:dest -> r:list B.instr -> r1:list B.instr ->
      r':list B.instr -> comp c g (top + 1) a (DSlot top) r r1 ->
      comp c ((x, top) :: g) (top + 1) b dst r1 r' -> comp c g top (ELet x a b) dst r r'
  | C_alias : g:env -> top:nat -> x:name -> y:name -> s:nat -> b:expr -> dst:dest -> r:list B.instr ->
      r':list B.instr -> squash (lookup y g == Some s) ->
      comp c ((x, s) :: g) top b dst r r' -> comp c g top (ELet x (EVar y) b) dst r r'
  | C_if_slot : g:env -> top:nat -> t:expr -> a:expr -> b:expr -> d:nat -> l:nat -> e0:nat ->
      r:list B.instr -> r1:list B.instr -> r3:list B.instr -> r':list B.instr ->
      compT c g top t l r r1 ->
      comp c g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> squash (lbl c l == Some r3) ->
      comp c g top b (DSlot d) r3 (B.ILabel e0 :: r') -> squash (lbl c e0 == Some r') ->
      comp c g top (EIf t a b) (DSlot d) r r'
  | C_if_ret : g:env -> top:nat -> t:expr -> a:expr -> b:expr -> l:nat ->
      r:list B.instr -> r1:list B.instr -> r3:list B.instr -> r':list B.instr ->
      compT c g top t l r r1 ->
      comp c g top a DRet r1 (B.ILabel l :: r3) -> squash (lbl c l == Some r3) -> comp c g top b DRet r3 r' ->
      comp c g top (EIf t a b) DRet r r'
  | C_cond_nil : g:env -> top:nat -> d:nat -> r:list B.instr ->
      comp c g top (ECond []) (DSlot d) (B.IPrim d B.PRaiseCond [] :: r) r
  | C_cond_true : g:env -> top:nat -> x:expr -> rest:list (expr & expr) -> dst:dest -> r:list B.instr ->
      r':list B.instr -> comp c g top x dst r r' ->
      comp c g top (ECond ((EBool true, x) :: rest)) dst r r'
  | C_cond_slot : g:env -> top:nat -> t:expr -> a:expr -> rest:list (expr & expr) -> d:nat -> l:nat -> e0:nat ->
      r:list B.instr -> r1:list B.instr -> r3:list B.instr -> r':list B.instr ->
      compT c g top t l r r1 ->
      comp c g top a (DSlot d) r1 (B.IJump e0 :: B.ILabel l :: r3) -> squash (lbl c l == Some r3) ->
      comp c g top (ECond rest) (DSlot d) r3 (B.ILabel e0 :: r') -> squash (lbl c e0 == Some r') ->
      comp c g top (ECond ((t, a) :: rest)) (DSlot d) r r'
  | C_cond_ret : g:env -> top:nat -> t:expr -> a:expr -> rest:list (expr & expr) -> l:nat ->
      r:list B.instr -> r1:list B.instr -> r3:list B.instr -> r':list B.instr ->
      compT c g top t l r r1 ->
      comp c g top a DRet r1 (B.ILabel l :: r3) -> squash (lbl c l == Some r3) ->
      comp c g top (ECond rest) DRet r3 r' ->
      comp c g top (ECond ((t, a) :: rest)) DRet r r'
  | C_type : g:env -> top:nat -> e:expr -> dst:dest -> r:list B.instr -> r':list B.instr ->
      comp c g top e dst r r' -> comp c g top (EType e) dst r r'
  | C_and : g:env -> top:nat -> x:expr -> y:expr -> d:nat -> l:nat -> e0:nat -> kt:nat -> kf:nat ->
      r:list B.instr -> r1:list B.instr -> r':list B.instr ->
      compT c g top x l r r1 ->
      compT c g top y l r1 (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
      squash (konst c kt == Some (B.VBool true)) -> squash (konst c kf == Some (B.VBool false)) ->
      squash (lbl c l == Some (B.IConst d kf :: B.ILabel e0 :: r')) -> squash (lbl c e0 == Some r') ->
      comp c g top (EAnd x y) (DSlot d) r r'
  | C_or : g:env -> top:nat -> x:expr -> y:expr -> d:nat -> l:nat -> nx:nat -> th:nat -> e0:nat -> kt:nat -> kf:nat ->
      r:list B.instr -> r2:list B.instr -> r':list B.instr ->
      compT c g top x nx r (B.IJump th :: B.ILabel nx :: r2) ->
      squash (lbl c nx == Some r2) ->
      compT c g top y l r2 (B.ILabel th :: B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r') ->
      squash (lbl c th == Some (B.IConst d kt :: B.IJump e0 :: B.ILabel l :: B.IConst d kf :: B.ILabel e0 :: r')) ->
      squash (konst c kt == Some (B.VBool true)) -> squash (konst c kf == Some (B.VBool false)) ->
      squash (lbl c l == Some (B.IConst d kf :: B.ILabel e0 :: r')) -> squash (lbl c e0 == Some r') ->
      comp c g top (EOr x y) (DSlot d) r r'
  | C_ret : g:env -> top:nat -> e:expr -> o:B.operand -> top2:nat -> r:list B.instr -> r':list B.instr ->
      compOp c g top e o top2 r (B.IReturn o :: r') -> comp c g top e DRet r r'
  | C_call : g:env -> top:nat -> f:name -> args:list expr -> d:nat -> n:nat -> i:B.instr ->
      r:list B.instr -> r':list B.instr -> squash (not_prim_name f) -> squash (n = length args) ->
      compW c g (top + 2) args r (i :: r') -> squash (call_instr i d top (B.sym_of_text f) n) ->
      comp c g top (ECall f args) (DSlot d) r r'
  | C_tail : g:env -> top:nat -> f:name -> args:list expr -> n:nat -> t:nat -> i:B.instr ->
      r:list B.instr -> r':list B.instr -> squash (not_prim_name f) -> squash (n = length args) ->
      squash (n + 2 <= t) -> squash (top <= t) -> compTA c g 2 t args [] r (i :: r') ->
      squash (tail_instr i 0 (B.sym_of_text f) n) ->
      comp c g top (ECall f args) DRet r r'
  | C_chain : g:env -> top:nat -> f:name -> a:expr -> e:expr -> v:value -> v':B.val_ -> k:nat -> d:nat ->
      r:list B.instr -> r':list B.instr -> squash (prim_of_name f == Some PCons) ->
      squash (lit_val a == Some v) -> squash (konst c k == Some v') -> vr v v' ->
      comp c g top e (DSlot d) r (B.IPrim d B.PCons [B.OConst k; B.OSlot d] :: r') ->
      comp c g top (ECall f [a; e]) (DSlot d) r r'

and compT (c : B.code) : env -> nat -> expr -> nat -> list B.instr -> list B.instr -> Type0 =
  | T_leaf : g:env -> top:nat -> e:expr -> o:B.operand -> top2:nat -> l:nat -> r:list B.instr -> r':list B.instr ->
      compOp c g top e o top2 r (B.IJumpIfFalse o l :: r') -> compT c g top e l r r'
  | T_and : g:env -> top:nat -> x:expr -> y:expr -> l:nat -> r:list B.instr -> r1:list B.instr -> r':list B.instr ->
      compT c g top x l r r1 -> compT c g top y l r1 r' -> compT c g top (EAnd x y) l r r'
  | T_or : g:env -> top:nat -> x:expr -> y:expr -> l:nat -> nx:nat -> th:nat ->
      r:list B.instr -> r2:list B.instr -> r':list B.instr ->
      compT c g top x nx r (B.IJump th :: B.ILabel nx :: r2) ->
      squash (lbl c nx == Some r2) -> compT c g top y l r2 (B.ILabel th :: r') -> squash (lbl c th == Some r') ->
      compT c g top (EOr x y) l r r'
  | T_let : g:env -> top:nat -> x:name -> a:expr -> b:expr -> l:nat -> r:list B.instr -> r1:list B.instr ->
      r':list B.instr -> comp c g (top + 1) a (DSlot top) r r1 ->
      compT c ((x, top) :: g) (top + 1) b l r1 r' -> compT c g top (ELet x a b) l r r'
  | T_alias : g:env -> top:nat -> x:name -> y:name -> s:nat -> b:expr -> l:nat -> r:list B.instr ->
      r':list B.instr -> squash (lookup y g == Some s) ->
      compT c ((x, s) :: g) top b l r r' -> compT c g top (ELet x (EVar y) b) l r r'
  | T_type : g:env -> top:nat -> e:expr -> l:nat -> r:list B.instr -> r':list B.instr ->
      compT c g top e l r r' -> compT c g top (EType e) l r r'

and compOp (c : B.code) : env -> nat -> expr -> B.operand -> nat -> list B.instr -> list B.instr -> Type0 =
  | O_var : g:env -> top:nat -> x:name -> s:nat -> r:list B.instr ->
      squash (lookup x g == Some s) -> squash (s < top) -> compOp c g top (EVar x) (B.OSlot s) top r r
  | O_lit : g:env -> top:nat -> e:expr -> v:value -> v':B.val_ -> k:nat -> r:list B.instr ->
      squash (lit_val e == Some v) -> squash (konst c k == Some v') -> vr v v' ->
      compOp c g top e (B.OConst k) top r r
  | O_val : g:env -> top:nat -> e:expr -> r:list B.instr -> r':list B.instr ->
      comp c g (top + 1) e (DSlot top) r r' ->
      compOp c g top e (B.OSlot top) (top + 1) r r'
  | O_type : g:env -> top:nat -> e:expr -> o:B.operand -> top2:nat -> r:list B.instr -> r':list B.instr ->
      compOp c g top e o top2 r r' -> compOp c g top (EType e) o top2 r r'

and compOps (c : B.code) : env -> nat -> list expr -> list B.operand -> list B.instr -> list B.instr -> Type0 =
  | Os_nil : g:env -> top:nat -> r:list B.instr -> compOps c g top [] [] r r
  | Os_cons : g:env -> top:nat -> e:expr -> es:list expr -> o:B.operand -> os:list B.operand -> top2:nat ->
      r:list B.instr -> r1:list B.instr -> r':list B.instr ->
      compOp c g top e o top2 r r1 ->
      compOps c g top2 es os r1 r' -> compOps c g top (e :: es) (o :: os) r r'

and compW (c : B.code) : env -> nat -> list expr -> list B.instr -> list B.instr -> Type0 =
  | W_nil : g:env -> s:nat -> r:list B.instr -> compW c g s [] r r
  | W_cons : g:env -> s:nat -> e:expr -> es:list expr -> r:list B.instr -> r1:list B.instr -> r':list B.instr ->
      comp c g (s + 1) e (DSlot s) r r1 -> compW c g (s + 1) es r1 r' ->
      compW c g s (e :: es) r r'

and compTA (c : B.code) : env -> nat -> nat -> list expr -> list (nat & nat) -> list B.instr -> list B.instr -> Type0 =
  | TA_nil : g:env -> s:nat -> t:nat -> ms:list (nat & nat) -> r':list B.instr ->
      compTA c g s t [] ms (app (moves ms) r') r'
  | TA_same : g:env -> s:nat -> t:nat -> x:name -> es:list expr -> ms:list (nat & nat) ->
      r:list B.instr -> r':list B.instr -> squash (lookup x g == Some s) -> compTA c g (s + 1) t es ms r r' ->
      compTA c g s t (EVar x :: es) ms r r'
  | TA_temp : g:env -> s:nat -> t:nat -> e:expr -> es:list expr -> ms:list (nat & nat) ->
      r:list B.instr -> r1:list B.instr -> r':list B.instr -> comp c g (t + 1) e (DSlot t) r r1 ->
      compTA c g (s + 1) (t + 1) es ((s, t) :: ms) r1 r' -> compTA c g s t (e :: es) ms r r'
  | TA_direct : g:env -> s:nat -> t:nat -> e:expr -> es:list expr -> ms:list (nat & nat) ->
      r:list B.instr -> r1:list B.instr -> r':list B.instr -> comp c g t e (DSlot s) r r1 ->
      compTA c (kill s g) (s + 1) t es ms r1 r' -> compTA c g s t (e :: es) ms r r'

(* Rocq Props become F* types; `inhabited t` is the proposition that t has a proof (in this F*, squash takes a prop). *)
let inhabited (t : Type0) : prop = exists (_ : t). True

(* A function's code: its body lowered with the parameters in slots 2 up. *)
let compFn (c : B.code) (ps : list name) (b : expr) : prop =
  exists (r' : list B.instr). (inhabited (comp c (bind ps 2) (2 + length ps) b DRet (B.code_ins c) r'))
