(* Port of rocq/JitLowerKont.v: the continuation relation behind the simulation, and stack facts.
   Encoding: KD/TK/KC/RK are mutual inductive F* types (Rocq: mutual Props with a combined
   induction scheme, which F* does not need: K_stable recurses on the derivation). The write set
   `w : N -> Prop` is `nat -> prop`; Prop premises are squash fields. *)
module Buri.JitLowerKont
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.JitLowerRel
module B = Buri.JitBytecode
module M = Buri.JitMeta

(* ---------- stack facts ---------- *)
(* `unfold`: with slotv folded, Z3 failed to instantiate menv's quantifier (two existentials over a
   nat-bound variable under slotv); unfolded, the same statements go through. *)
unfold let slotv (st : B.tree B.val_) (a : nat) : option B.val_ = B.tget (B.skey a) st

let skey_inj (a b : nat) : Lemma (requires B.skey a == B.skey b) (ensures a == b) = ()
let slotv_same (st : B.tree B.val_) (a : nat) (v : B.val_) : Lemma (slotv (B.tset (B.skey a) v st) a == Some v) =
  M.tget_tset_same (B.skey a) v st
let slotv_other (st : B.tree B.val_) (a b : nat) (v : B.val_)
  : Lemma (requires a <> b) (ensures slotv (B.tset (B.skey b) v st) a == slotv st a) =
  M.tget_tset_other (B.skey a) (B.skey b) v st

(* Rocq: forall x s, lookup x g = Some s -> exists v v', ... . Stated with the match on
   `lookup x g` (same meaning) and a pattern, because Z3 did not reliably instantiate the
   two-variable form inside larger contexts. *)
let menv (fp : nat) (st : B.tree B.val_) (g : env) (rho : lenv) : prop =
  forall (x : name). {:pattern (lookup x g)} (match lookup x g with
    | Some s -> exists v v'. lookup x rho == Some v /\ slotv st (fp + s) == Some v' /\ vrp v v'
    | None -> True)
let envBelow (g : env) (top : nat) : prop = forall (x : name) (s : nat). lookup x g == Some s ==> s < top
let prot (g : env) (fp : nat) (w : nat -> prop) : prop = forall (x : name) (s : nat). lookup x g == Some s ==> ~(w (fp + s))
let above (fp top : nat) (w : nat -> prop) : prop = forall (a : nat). fp + top <= a ==> w a
let sub (w w1 : nat -> prop) : prop = forall (a : nat). w a ==> w1 a

let read_o (c : B.code) (fp : nat) (st : B.tree B.val_) (o : B.operand) : option B.val_ =
  match o with
  | B.OSlot s -> slotv st (fp + s)
  | B.OConst k -> nth_error (B.code_consts c) k
let o_safe (fp : nat) (w : nat -> prop) (o : B.operand) : prop =
  match o with B.OSlot s -> ~(w (fp + s)) | B.OConst _ -> True
let o_below (top : nat) (o : B.operand) : prop =
  match o with B.OSlot s -> s < top | B.OConst _ -> True

noeq type doneR (c : B.code) (fp : nat) (st : B.tree B.val_) : list value -> list B.operand -> Type0 =
  | DR_nil : doneR c fp st [] []
  | DR_cons : v:value -> v':B.val_ -> o:B.operand -> vs:list value -> os:list B.operand ->
      squash (read_o c fp st o == Some v') -> vr v v' -> doneR c fp st vs os ->
      doneR c fp st (v :: vs) (o :: os)

noeq type argsAt (st : B.tree B.val_) : nat -> list value -> Type0 =
  | AA_nil : a:nat -> argsAt st a []
  | AA_cons : a:nat -> v:value -> v':B.val_ -> vs:list value -> squash (slotv st a == Some v') -> vr v v' ->
      argsAt st (a + 1) vs -> argsAt st a (v :: vs)

let rec loc (ms : list (nat & nat)) (i : nat) : nat = match ms with
  | [] -> i | (s, t) :: ms -> if s = i then t else loc ms i

noeq type paramAt (fp : nat) (st : B.tree B.val_) (ms : list (nat & nat)) : nat -> list value -> Type0 =
  | PA_nil : i:nat -> paramAt fp st ms i []
  | PA_cons : i:nat -> v:value -> v':B.val_ -> vs:list value ->
      squash (slotv st (fp + loc ms i) == Some v') -> vr v v' ->
      paramAt fp st ms (i + 1) vs -> paramAt fp st ms i (v :: vs)

noeq type kD : B.code -> nat -> B.tree B.val_ -> list B.cont -> (nat -> prop) -> B.operand ->
    list B.instr -> list frame -> Type0 =
  | KD_ret : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> o:B.operand ->
      r:list B.instr -> k:list frame -> squash (sub w (fun a -> fp <= a)) -> rK fp st cs k ->
      kD c fp st cs w o (B.IReturn o :: r) k
  | KD_jump : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> o:B.operand ->
      e:nat -> r:list B.instr -> r1:list B.instr -> k:list frame -> squash (lbl c e == Some r1) ->
      kD c fp st cs w o r1 k -> kD c fp st cs w o (B.IJump e :: r) k
  | KD_label : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> o:B.operand ->
      l:nat -> r:list B.instr -> k:list frame -> kD c fp st cs w o r k -> kD c fp st cs w o (B.ILabel l :: r) k
  | KD_let : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> d:nat ->
      r:list B.instr -> x:name -> b:expr -> rho:lenv -> k1:list frame -> g:env -> top:nat -> dst:dest ->
      r2:list B.instr -> w1:(nat -> prop) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g top) -> squash (d < top) ->
      comp c ((x, d) :: g) top b dst r r2 -> squash (sub w w1) -> squash (above fp top w1) ->
      kC c fp st cs w1 dst r2 k1 ->
      kD c fp st cs w (B.OSlot d) r (KLet x b rho :: k1)
  | KD_lett : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> d:nat ->
      r:list B.instr -> x:name -> b:expr -> rho:lenv -> k1:list frame -> g:env -> top:nat -> l:nat ->
      r2:list B.instr -> w1:(nat -> prop) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g top) -> squash (d < top) ->
      compT c ((x, d) :: g) top b l r r2 -> squash (sub w w1) -> squash (above fp top w1) ->
      tK c fp st cs w1 true l r2 k1 ->
      kD c fp st cs w (B.OSlot d) r (KLet x b rho :: k1)
  | KD_test : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> o:B.operand ->
      l:nat -> r:list B.instr -> k:list frame -> tK c fp st cs w true l r k ->
      kD c fp st cs w o (B.IJumpIfFalse o l :: r) k
  | KD_prim : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> o:B.operand ->
      r:list B.instr -> f:name -> p:prim -> q:B.prim -> vals:list value -> es:list expr -> rho:lenv ->
      k1:list frame -> g:env -> top:nat -> ops:list B.operand -> dops:list B.operand -> d:nat ->
      r1:list B.instr -> w1:(nat -> prop) ->
      squash (prim_of_name f == Some p) -> squash (pmap p == Some q) ->
      squash (length vals + 1 + length es = prim_arity p) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g top) ->
      compOps c g top es ops r (B.IPrim d q (app (rev dops) (o :: ops)) :: r1) ->
      doneR c fp st vals dops -> squash (forall_l (o_safe fp w) dops) ->
      squash (forall_l (o_below top) dops) -> squash (o_below top o) ->
      squash (sub w w1) -> squash (above fp top w1) -> squash (w1 (fp + d)) -> kD c fp st cs w1 (B.OSlot d) r1 k1 ->
      kD c fp st cs w o r (KCallArgs f vals es rho :: k1)
  | KD_call : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) ->
      r:list B.instr -> f:name -> vals:list value -> es:list expr -> rho:lenv -> k1:list frame -> g:env ->
      a:nat -> s:nat -> d:nat -> n:nat -> i:B.instr -> r1:list B.instr -> w1:(nat -> prop) ->
      squash (not_prim_name f) -> squash (s = a + 2 + length vals) ->
      squash (n = length vals + 1 + length es) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g (s + 1)) ->
      compW c g (s + 1) es r (i :: r1) -> squash (call_instr i d a (B.sym_of_text f) n) ->
      argsAt st (fp + a + 2) (rev vals) -> squash (sub w (fun x -> fp + s <= x)) ->
      squash (sub w w1) -> squash (above fp a w1) -> squash (w1 (fp + d)) -> kD c fp st cs w1 (B.OSlot d) r1 k1 ->
      kD c fp st cs w (B.OSlot s) r (KCallArgs f vals es rho :: k1)
  | KD_tail : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> o:B.operand ->
      r:list B.instr -> f:name -> vals:list value -> es:list expr -> rho:lenv -> k1:list frame -> g:env ->
      s:nat -> t:nat -> t0:nat -> ms:list (nat & nat) -> n:nat -> i:B.instr -> r1:list B.instr ->
      squash (not_prim_name f) -> squash (s = 2 + length vals) ->
      squash (n = length vals + 1 + length es) -> squash (n + 2 <= t0) -> squash (t0 <= t) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g t) ->
      compTA c g (s + 1) t es ms r (i :: r1) -> squash (tail_instr i 0 (B.sym_of_text f) n) ->
      squash (o == B.OSlot (loc ms s)) -> squash (loc ms s < t) ->
      squash (forall_l (fun (m : nat & nat) -> 2 <= fst m /\ fst m < s + 1 /\ n + 2 <= snd m /\ snd m < t) ms) ->
      squash (nodup_l (map fst ms)) ->
      squash (forall (j : nat). 2 <= j /\ j < s ==> loc ms j = j \/ (n + 2 <= loc ms j /\ loc ms j < t0)) ->
      paramAt fp st ms 2 (rev vals) ->
      squash (sub w (fun x -> x = fp + s \/ fp + t0 <= x)) -> rK fp st cs k1 ->
      kD c fp st cs w o r (KCallArgs f vals es rho :: k1)

and tK : B.code -> nat -> B.tree B.val_ -> list B.cont -> (nat -> prop) -> bool -> nat ->
    list B.instr -> list frame -> Type0 =
  | TK_if : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> l:nat ->
      r:list B.instr -> a:expr -> b:expr -> rho:lenv -> k1:list frame -> g:env -> top:nat -> dst:dest ->
      r2:list B.instr -> r3:list B.instr -> r4:list B.instr -> w1:(nat -> prop) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g top) ->
      comp c g top a dst r r2 -> squash (lbl c l == Some r3) -> comp c g top b dst r3 r4 ->
      squash (sub w w1) -> squash (above fp top w1) -> kC c fp st cs w1 dst r2 k1 -> kC c fp st cs w1 dst r4 k1 ->
      tK c fp st cs w true l r (KIf a b rho :: k1)
  | TK_cond : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> l:nat ->
      r:list B.instr -> a:expr -> rest:list (expr & expr) -> rho:lenv -> k1:list frame -> g:env -> top:nat ->
      dst:dest -> r2:list B.instr -> r3:list B.instr -> r4:list B.instr -> w1:(nat -> prop) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g top) ->
      comp c g top a dst r r2 -> squash (lbl c l == Some r3) -> comp c g top (ECond rest) dst r3 r4 ->
      squash (sub w w1) -> squash (above fp top w1) -> kC c fp st cs w1 dst r2 k1 -> kC c fp st cs w1 dst r4 k1 ->
      tK c fp st cs w true l r (KCond a rest rho :: k1)
  | TK_and : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> gd:bool -> l:nat ->
      r:list B.instr -> y:expr -> rho:lenv -> k1:list frame -> g:env -> top:nat -> r2:list B.instr ->
      w1:(nat -> prop) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g top) ->
      compT c g top y l r r2 -> squash (sub w w1) -> squash (above fp top w1) ->
      tK c fp st cs w1 gd l r2 k1 ->
      tK c fp st cs w true l r (KAnd y rho :: k1)
  | TK_andr : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> gd:bool -> l:nat ->
      r:list B.instr -> k1:list frame -> w1:(nat -> prop) -> squash (sub w w1) -> tK c fp st cs w1 gd l r k1 ->
      tK c fp st cs w true l r (KAndR :: k1)
  | TK_or : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> gd:bool -> l:nat ->
      nx:nat -> r1:list B.instr -> y:expr -> rho:lenv -> k1:list frame -> g:env -> top:nat ->
      r2:list B.instr -> r3:list B.instr -> w1:(nat -> prop) ->
      squash (menv fp st g rho) -> squash (prot g fp w) -> squash (envBelow g top) ->
      squash (lbl c nx == Some r2) -> compT c g top y l r2 r3 -> squash (sub w w1) -> squash (above fp top w1) ->
      tK c fp st cs w1 gd l r3 k1 -> tK c fp st cs w1 gd l r1 k1 ->
      tK c fp st cs w true nx r1 (KOr y rho :: k1)
  | TK_orr : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> gd:bool -> l:nat ->
      r:list B.instr -> k1:list frame -> w1:(nat -> prop) -> squash (sub w w1) -> tK c fp st cs w1 gd l r k1 ->
      tK c fp st cs w true l r (KOrR :: k1)
  | TK_jump : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> gd:bool -> l:nat ->
      e:nat -> r:list B.instr -> r1:list B.instr -> k:list frame -> squash (lbl c e == Some r1) ->
      tK c fp st cs w gd l r1 k -> tK c fp st cs w gd l (B.IJump e :: r) k
  | TK_label : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> gd:bool -> l:nat ->
      x:nat -> r:list B.instr -> k:list frame -> tK c fp st cs w gd l r k ->
      tK c fp st cs w gd l (B.ILabel x :: r) k
  | TK_value : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> l:nat -> d:nat ->
      kt:nat -> kf:nat -> r2:list B.instr -> r4:list B.instr -> k:list frame -> w1:(nat -> prop) ->
      squash (konst c kt == Some (B.VBool true)) -> squash (konst c kf == Some (B.VBool false)) ->
      squash (lbl c l == Some (B.IConst d kf :: r4)) -> squash (sub w w1) -> squash (w1 (fp + d)) ->
      kD c fp st cs w1 (B.OSlot d) r2 k -> kD c fp st cs w1 (B.OSlot d) r4 k ->
      tK c fp st cs w false l (B.IConst d kt :: r2) k

and kC : B.code -> nat -> B.tree B.val_ -> list B.cont -> (nat -> prop) -> dest ->
    list B.instr -> list frame -> Type0 =
  | KC_ret : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> r:list B.instr ->
      k:list frame -> squash (sub w (fun a -> fp <= a)) -> rK fp st cs k -> kC c fp st cs w DRet r k
  | KC_slot : c:B.code -> fp:nat -> st:B.tree B.val_ -> cs:list B.cont -> w:(nat -> prop) -> d:nat ->
      r:list B.instr -> k:list frame -> squash (w (fp + d)) -> kD c fp st cs w (B.OSlot d) r k ->
      kC c fp st cs w (DSlot d) r k

and rK : nat -> B.tree B.val_ -> list B.cont -> list frame -> Type0 =
  | RK_top : fp:nat -> st:B.tree B.val_ -> rK fp st [] []
  | RK_call : fp:nat -> st:B.tree B.val_ -> c:B.code -> r:list B.instr -> d:nat -> a:nat -> cs:list B.cont ->
      k:list frame -> w:(nat -> prop) -> squash (a <= fp) -> squash (above (fp - a) a w) ->
      kD c (fp - a) st cs w (B.OSlot d) r k -> squash (w (fp - a + d)) ->
      rK fp st (B.mkCont c r d a :: cs) k
