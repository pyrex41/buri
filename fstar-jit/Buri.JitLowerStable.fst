(* Port of rocq/JitLowerStable.v: what writes to the stack leave intact. K_stable is a mutually
   recursive function over the KD/TK/KC/RK derivation (Rocq: induction with the combined scheme). *)
module Buri.JitLowerStable
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.JitLowerRel
open Buri.JitLowerKont
module B = Buri.JitBytecode

let same_off (st st' : B.tree B.val_) (w : nat -> prop) : prop = forall (a : nat). ~(w a) ==> slotv st a == slotv st' a

let menv_stable (fp : nat) (st st' : B.tree B.val_) (g : env) (rho : lenv) (w : nat -> prop)
  : Lemma (requires menv fp st g rho /\ prot g fp w /\ same_off st st' w) (ensures menv fp st' g rho) =
  introduce forall (x : name). (match lookup x g with
    | Some s -> exists v v'. lookup x rho == Some v /\ slotv st' (fp + s) == Some v' /\ vrp v v'
    | None -> True)
  with (match lookup x g with
    | Some s -> assert (~(w (fp + s))); assert (slotv st (fp + s) == slotv st' (fp + s))
    | None -> ())

let rec doneR_stable (c : B.code) (fp : nat) (st st' : B.tree B.val_) (w : nat -> prop)
  (vs : list value) (os : list B.operand) (d : doneR c fp st vs os)
  : Pure (doneR c fp st' vs os) (requires forall_l (o_safe fp w) os /\ same_off st st' w)
    (ensures fun _ -> True) (decreases d) =
  match d with
  | DR_nil -> DR_nil
  | DR_cons v v' o vs1 os1 _ dv rest -> DR_cons v v' o vs1 os1 () dv (doneR_stable c fp st st' w vs1 os1 rest)

let rec argsAt_stable (st st' : B.tree B.val_) (a0 : nat) (vs : list value) (d : argsAt st a0 vs)
  : Pure (argsAt st' a0 vs)
    (requires forall (a : nat). a0 <= a /\ a < a0 + length vs ==> slotv st a == slotv st' a)
    (ensures fun _ -> True) (decreases d) =
  match d with
  | AA_nil a -> AA_nil a
  | AA_cons a v v' vs1 _ dv rest -> AA_cons a v v' vs1 () dv (argsAt_stable st st' (a + 1) vs1 rest)

let rec loc_range (ms : list (nat & nat)) (i n t : nat)
  : Lemma (requires forall_l (fun (m : nat & nat) -> n + 2 <= snd m /\ snd m < t) ms)
          (ensures loc ms i = i \/ (n + 2 <= loc ms i /\ loc ms i < t)) =
  match ms with [] -> () | (s, u) :: ms' -> if s = i then () else loc_range ms' i n t

let rec paramAt_stable (fp : nat) (st st' : B.tree B.val_) (ms : list (nat & nat)) (i : nat) (vs : list value)
  (d : paramAt fp st ms i vs)
  : Pure (paramAt fp st' ms i vs)
    (requires forall (j : nat). i <= j /\ j < i + length vs ==> slotv st (fp + loc ms j) == slotv st' (fp + loc ms j))
    (ensures fun _ -> True) (decreases d) =
  match d with
  | PA_nil i -> PA_nil i
  | PA_cons i v v' vs1 _ dv rest -> PA_cons i v v' vs1 () dv (paramAt_stable fp st st' ms (i + 1) vs1 rest)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec kD_stable (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#o : B.operand) (#r : list B.instr) (#k : list frame) (d : kD c fp st cs w o r k) (st' : B.tree B.val_)
  : Pure (kD c fp st' cs w o r k) (requires same_off st st' w) (ensures fun _ -> True) (decreases d) =
  match d with
  | KD_ret c fp st cs w o r k _ rk -> KD_ret c fp st' cs w o r k () (rK_stable rk st')
  | KD_jump c fp st cs w o e r r1 k _ d1 -> KD_jump c fp st' cs w o e r r1 k () (kD_stable d1 st')
  | KD_label c fp st cs w o l r k d1 -> KD_label c fp st' cs w o l r k (kD_stable d1 st')
  | KD_let c fp st cs w dd r x b rho k1 g top dst r2 w1 _ _ _ _ dc _ _ kc ->
    menv_stable fp st st' g rho w;
    KD_let c fp st' cs w dd r x b rho k1 g top dst r2 w1 () () () () dc () () (kC_stable kc st')
  | KD_lett c fp st cs w dd r x b rho k1 g top l r2 w1 _ _ _ _ dc _ _ tk ->
    menv_stable fp st st' g rho w;
    KD_lett c fp st' cs w dd r x b rho k1 g top l r2 w1 () () () () dc () () (tK_stable tk st')
  | KD_test c fp st cs w o l r k tk -> KD_test c fp st' cs w o l r k (tK_stable tk st')
  | KD_prim c fp st cs w o r f p q vals es rho k1 g top ops dops dd r1 w1 _ _ _ _ _ _ cops dr _ _ _ _ _ _ kd ->
    menv_stable fp st st' g rho w;
    KD_prim c fp st' cs w o r f p q vals es rho k1 g top ops dops dd r1 w1 () () () () () () cops
      (doneR_stable c fp st st' w vals dops dr) () () () () () () (kD_stable kd st')
  | KD_call c fp st cs w r f vals es rho k1 g a s dd n i r1 w1 _ _ _ _ _ _ cw _ aa _ _ _ _ kd ->
    menv_stable fp st st' g rho w;
    rev_length vals;
    KD_call c fp st' cs w r f vals es rho k1 g a s dd n i r1 w1 () () () () () () cw ()
      (argsAt_stable st st' (fp + a + 2) (rev vals) aa) () () () () (kD_stable kd st')
  | KD_tail c fp st cs w o r f vals es rho k1 g s t t0 ms n i r1 _ _ _ _ _ _ _ _ cta _ _ _ _ _ _ pa _ rk ->
    menv_stable fp st st' g rho w;
    rev_length vals;
    KD_tail c fp st' cs w o r f vals es rho k1 g s t t0 ms n i r1 () () () () () () () () cta () () () () () ()
      (paramAt_stable fp st st' ms 2 (rev vals) pa) () (rK_stable rk st')

and tK_stable (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#gd : bool) (#l : nat) (#r : list B.instr) (#k : list frame) (d : tK c fp st cs w gd l r k) (st' : B.tree B.val_)
  : Pure (tK c fp st' cs w gd l r k) (requires same_off st st' w) (ensures fun _ -> True) (decreases d) =
  match d with
  | TK_if c fp st cs w l r a b rho k1 g top dst r2 r3 r4 w1 _ _ _ ca _ cb _ _ kc1 kc2 ->
    menv_stable fp st st' g rho w;
    TK_if c fp st' cs w l r a b rho k1 g top dst r2 r3 r4 w1 () () () ca () cb () () (kC_stable kc1 st') (kC_stable kc2 st')
  | TK_cond c fp st cs w l r a rest rho k1 g top dst r2 r3 r4 w1 _ _ _ ca _ cb _ _ kc1 kc2 ->
    menv_stable fp st st' g rho w;
    TK_cond c fp st' cs w l r a rest rho k1 g top dst r2 r3 r4 w1 () () () ca () cb () () (kC_stable kc1 st') (kC_stable kc2 st')
  | TK_and c fp st cs w gd l r y rho k1 g top r2 w1 _ _ _ cy _ _ tk ->
    menv_stable fp st st' g rho w;
    TK_and c fp st' cs w gd l r y rho k1 g top r2 w1 () () () cy () () (tK_stable tk st')
  | TK_andr c fp st cs w gd l r k1 w1 _ tk -> TK_andr c fp st' cs w gd l r k1 w1 () (tK_stable tk st')
  | TK_or c fp st cs w gd l nx r1 y rho k1 g top r2 r3 w1 _ _ _ _ cy _ _ tk1 tk2 ->
    menv_stable fp st st' g rho w;
    TK_or c fp st' cs w gd l nx r1 y rho k1 g top r2 r3 w1 () () () () cy () () (tK_stable tk1 st') (tK_stable tk2 st')
  | TK_orr c fp st cs w gd l r k1 w1 _ tk -> TK_orr c fp st' cs w gd l r k1 w1 () (tK_stable tk st')
  | TK_jump c fp st cs w gd l e r r1 k _ tk -> TK_jump c fp st' cs w gd l e r r1 k () (tK_stable tk st')
  | TK_label c fp st cs w gd l x r k tk -> TK_label c fp st' cs w gd l x r k (tK_stable tk st')
  | TK_value c fp st cs w l dd kt kf r2 r4 k w1 _ _ _ _ _ kd1 kd2 ->
    TK_value c fp st' cs w l dd kt kf r2 r4 k w1 () () () () () (kD_stable kd1 st') (kD_stable kd2 st')

and kC_stable (#c : B.code) (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#w : nat -> prop)
  (#dst : dest) (#r : list B.instr) (#k : list frame) (d : kC c fp st cs w dst r k) (st' : B.tree B.val_)
  : Pure (kC c fp st' cs w dst r k) (requires same_off st st' w) (ensures fun _ -> True) (decreases d) =
  match d with
  | KC_ret c fp st cs w r k _ rk -> KC_ret c fp st' cs w r k () (rK_stable rk st')
  | KC_slot c fp st cs w dd r k _ kd -> KC_slot c fp st' cs w dd r k () (kD_stable kd st')

and rK_stable (#fp : nat) (#st : B.tree B.val_) (#cs : list B.cont) (#k : list frame)
  (d : rK fp st cs k) (st' : B.tree B.val_)
  : Pure (rK fp st' cs k) (requires forall (a : nat). a < fp ==> slotv st a == slotv st' a) (ensures fun _ -> True) (decreases d) =
  match d with
  | RK_top fp st -> RK_top fp st'
  | RK_call fp st c r dd a cs k w _ _ kd _ -> RK_call fp st' c r dd a cs k w () () (kD_stable kd st') ()
#pop-options
