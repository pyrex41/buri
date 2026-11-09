(* Compatibility lemmas for KRef that rocq/JitLowerEquiv.v (670d29d) states and leaves UNPROVED:
   compat_let_statement and compat_if_statement. Proved here, together with two more statements
   Rocq leaves unproved that they need: VRel_wext_statement and VRel_down_statement. *)
module Buri.JitLowerCompatNeg
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.KLPort
open Buri.JitLowerStep
open Buri.JitLowerEquiv
module B = Buri.JitBytecode

(* ---------- one step back, on both sides (generalizes obsT_tau_back) ---------- *)
let not_final_shape (c : config) : prop = Eval? c.ctl \/ Cons? c.kont

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let obsT_back (sealed : list name) (j : nat) (w : world) (c0 c0' c c1 : config)
  : Lemma (requires not_final_shape c /\
                    next_r (rr sealed) pr c0 == MTau c0' /\ next_r (rr sealed) pr c == MTau c1 /\
                    obsT sealed j w c0' c1 /\
                    (running_state c = true ==> running_state c0 = true /\
                       (forall (x : exn). obsT sealed j w (cfg (Throw x) c0.kont c0.mem) (cfg (Throw x) c.kont c.mem))))
          (ensures obsT sealed j w c0 c) =
  introduce forall (n : nat) (t : trace) (c' : config). n < j ==> (forall (h : runs sealed n c t c').
   (forall v s. c' == cfg (Ret v) [] s ==> (exists v0 s0 w'.
      srun sealed c0 t (cfg (Ret v0) [] s0) /\ wext w w' /\ gVal w' v0 v /\ gStore w' s0 s)) /\
   (forall x s. c' == cfg (Throw x) [] s ==> (exists s0 w'.
      srun sealed c0 t (cfg (Throw x) [] s0) /\ wext w w' /\ gStore w' s0 s)) /\
   (forall why. next_r (rr sealed) pr c' == MWrong why ==> (exists c0' why0.
      srun sealed c0 t c0' /\ next_r (rr sealed) pr c0' == MWrong why0)))
  with introduce _ ==> _ with
  introduce forall (h : runs sealed n c t c'). _
  with (match h with
    | Runs_0 _ -> ()
    | Runs_S n1 _ l c1' t1 _ st rest ->
      (match st with
       | Step_r_tau _ _ _ ->
         introduce forall (c2 : config). srun sealed c0' t1 c2 ==> srun sealed c0 t1 c2
         with introduce _ ==> _ with srun_cons sealed c0 c0' c2 t1
       | Step_r_resource _ r x _ _ ->
         introduce forall (c2 : config). srun sealed (cfg (Throw x) c0.kont c0.mem) t1 c2 ==> srun sealed c0 t1 c2
         with introduce _ ==> _ with srun_cons_res sealed c0 r x c2 t1))
#pop-options

(* ---------- worlds ---------- *)
let wext_trans (w w' w'' : world) : Lemma (requires wext w w' /\ wext w' w'') (ensures wext w w'') = ()

(* ---------- VRel_wext and VRel_down (Rocq: unproved statements) ---------- *)
let rec vBody_wext (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w w' : world) (v0 v : value)
  : Lemma (requires wext w w' /\ vBody sealed dd vv k w v0 v) (ensures vBody sealed dd vv k w' v0 v) (decreases v0) =
  match v0, v with
  | VCons a0 d0, VCons a d -> vBody_wext sealed dd vv k w w' a0 a; vBody_wext sealed dd vv k w w' d0 d
  | VPartial _ l0, VPartial _ l -> vBody_list_wext sealed dd vv k w w' l0 l
  | VLam x0 b0 r0, VLam x b r ->
    introduce forall (j : nat) w''. j < k ==> wext w' w'' ==> wext w w''
    with introduce _ ==> _ with introduce _ ==> _ with wext_trans w w' w''
  | VFrozen b0 r0, VFrozen b r ->
    introduce forall (j : nat) w''. j < k ==> wext w' w'' ==> wext w w''
    with introduce _ ==> _ with introduce _ ==> _ with wext_trans w w' w''
  | _ -> ()
and vBody_list_wext (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w w' : world) (l0 l : list value)
  : Lemma (requires wext w w' /\ vBody_list sealed dd vv k w l0 l) (ensures vBody_list sealed dd vv k w' l0 l) (decreases l0) =
  match l0, l with
  | x0 :: r0, x :: r -> vBody_wext sealed dd vv k w w' x0 x; vBody_list_wext sealed dd vv k w w' r0 r
  | _ -> ()

let vRel_wext (sealed : list name) (dd : list (name & fundef)) (k : nat) (w w' : world) (v0 v : value)
  : Lemma (requires wext w w' /\ vRel sealed dd k w v0 v) (ensures vRel sealed dd k w' v0 v) =
  vRel_unfold sealed dd k w v0 v; vRel_unfold sealed dd k w' v0 v;
  vBody_wext sealed dd (if k = 0 then bottom_rel else vRelF sealed dd (k - 1)) k w w' v0 v

let equiv_below (vv vv' : vrelt) (j : nat) : prop =
  forall (i : nat) w x y. i < j ==> (vv i w x y <==> vv' i w x y)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec vBody_down (sealed : list name) (dd : list (name & fundef)) (vv vv' : vrelt) (k j : nat) (w : world) (v0 v : value)
  : Lemma (requires j <= k /\ equiv_below vv vv' j /\ vBody sealed dd vv k w v0 v) (ensures vBody sealed dd vv' j w v0 v)
    (decreases v0) =
  match v0, v with
  | VCons a0 d0, VCons a d -> vBody_down sealed dd vv vv' k j w a0 a; vBody_down sealed dd vv vv' k j w d0 d
  | VPartial _ l0, VPartial _ l -> vBody_list_down sealed dd vv vv' k j w l0 l
  | VLam x0 b0 r0, VLam x b r ->
    introduce forall (j' : nat). j' < j ==> (forall w'. wext w w' ==> (forall a0 a. vv' j' w' a0 a ==>
        eRel_with sealed dd vv' j' w' ((x0, a0) :: r0) b0 ((x, a) :: r) b))
    with introduce _ ==> _ with introduce forall w'. _ with introduce _ ==> _ with
    introduce forall a0 a. _ with introduce _ ==> _ with
      eRel_with_ext sealed dd vv vv' j' w' ((x0, a0) :: r0) b0 ((x, a) :: r) b
  | VFrozen b0 r0, VFrozen b r ->
    introduce forall (j' : nat). j' < j ==> (forall w'. wext w w' ==> eRel_with sealed dd vv' j' w' r0 b0 r b)
    with introduce _ ==> _ with introduce forall w'. _ with introduce _ ==> _ with
      eRel_with_ext sealed dd vv vv' j' w' r0 b0 r b
  | _ -> ()
and vBody_list_down (sealed : list name) (dd : list (name & fundef)) (vv vv' : vrelt) (k j : nat) (w : world) (l0 l : list value)
  : Lemma (requires j <= k /\ equiv_below vv vv' j /\ vBody_list sealed dd vv k w l0 l) (ensures vBody_list sealed dd vv' j w l0 l)
    (decreases l0) =
  match l0, l with
  | x0 :: r0, x :: r -> vBody_down sealed dd vv vv' k j w x0 x; vBody_list_down sealed dd vv vv' k j w r0 r
  | _ -> ()
#pop-options

let vRel_down (sealed : list name) (dd : list (name & fundef)) (k j : nat) (w : world) (v0 v : value)
  : Lemma (requires j <= k /\ vRel sealed dd k w v0 v) (ensures vRel sealed dd j w v0 v) =
  vRel_unfold sealed dd k w v0 v; vRel_unfold sealed dd j w v0 v;
  let vk = (if k = 0 then bottom_rel else vRelF sealed dd (k - 1)) in
  let vj = (if j = 0 then bottom_rel else vRelF sealed dd (j - 1)) in
  introduce forall (i : nat) w x y. i < j ==> (vk i w x y <==> vj i w x y)
  with introduce _ ==> _ with (vRelF_index sealed dd (k - 1) i w x y; vRelF_index sealed dd (j - 1) i w x y);
  vBody_down sealed dd vk vj k j w v0 v

(* Rocq: VRel_wext_statement and VRel_down_statement. *)
let vRel_wext_statement (sealed : list name) (dd : list (name & fundef)) : Lemma
  (forall (k : nat) w w' v0 v. wext w w' ==> vRel sealed dd k w v0 v ==> vRel sealed dd k w' v0 v) =
  introduce forall (k : nat) w w' v0 v. wext w w' ==> vRel sealed dd k w v0 v ==> vRel sealed dd k w' v0 v
  with introduce _ ==> _ with introduce _ ==> _ with vRel_wext sealed dd k w w' v0 v
let vRel_down_statement (sealed : list name) (dd : list (name & fundef)) : Lemma
  (forall (k j : nat) w v0 v. j <= k ==> vRel sealed dd k w v0 v ==> vRel sealed dd j w v0 v) =
  introduce forall (k j : nat) w v0 v. j <= k ==> vRel sealed dd k w v0 v ==> vRel sealed dd j w v0 v
  with introduce _ ==> _ with introduce _ ==> _ with vRel_down sealed dd k j w v0 v

(* ---------- environments and continuations ---------- *)
let envRel_mono (sealed : list name) (dd : list (name & fundef)) (k j : nat) (w w' : world) (g : list name) (rho0 rho : lenv)
  : Lemma (requires j <= k /\ wext w w' /\ envRel_with (vRel sealed dd k) w g rho0 rho)
          (ensures envRel_with (vRel sealed dd j) w' g rho0 rho) =
  introduce forall x. mem_l x g ==> (exists v0 v. lookup x rho0 == Some v0 /\ lookup x rho == Some v /\ vRel sealed dd j w' v0 v)
  with introduce _ ==> _ with
    eliminate exists v0 v. lookup x rho0 == Some v0 /\ lookup x rho == Some v /\ vRel sealed dd k w v0 v
    with (vRel_down sealed dd k j w v0 v; vRel_wext sealed dd j w w' v0 v)

let envRel_cons (sealed : list name) (dd : list (name & fundef)) (j : nat) (w : world) (g : list name) (rho0 rho : lenv)
  (x : name) (v0 v : value)
  : Lemma (requires envRel_with (vRel sealed dd j) w g rho0 rho /\ vRel sealed dd j w v0 v)
          (ensures envRel_with (vRel sealed dd j) w (x :: g) ((x, v0) :: rho0) ((x, v) :: rho)) =
  introduce forall y. mem_l y (x :: g) ==> (exists v0' v'. lookup y ((x, v0) :: rho0) == Some v0' /\
     lookup y ((x, v) :: rho) == Some v' /\ vRel sealed dd j w v0' v')
  with introduce _ ==> _ with (text_eqb_eq y x; if text_eqb y x then () else ())

let kRel_mono (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (j j' : nat) (w w' : world) (k0 kk : list frame)
  : Lemma (requires j' <= j /\ wext w w' /\ kRel_with sealed dd vv j w k0 kk) (ensures kRel_with sealed dd vv j' w' k0 kk) =
  introduce forall (w'' : world). wext w' w'' ==> wext w w''
  with introduce _ ==> _ with wext_trans w w' w''

(* The relation at index j, read in the family of index k (j <= k) or of index j. *)
let family_down (sealed : list name) (dd : list (name & fundef)) (k j : nat)
  : Lemma (requires j <= k) (ensures equiv_upto (vRelF sealed dd k) (vRelF sealed dd j) j) =
  introduce forall (i : nat) w x y. i <= j ==> (vRelF sealed dd k i w x y <==> vRelF sealed dd j i w x y)
  with introduce _ ==> _ with (vRelF_index sealed dd k i w x y; vRelF_index sealed dd j i w x y)

(* A raise passes a frame that does not catch, on both sides. *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let throw_frame (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (j j' : nat) (w w' : world)
  (f0 f : frame) (k0 kk : list frame) (x : exn) (s0 s : store)
  : Lemma (requires not (KTrap? f0) /\ not (KTrap? f) /\ j' <= j /\ wext w w' /\ kRel_with sealed dd vv j w k0 kk /\
                    sRel_with dd (vv j') w' s0 s)
          (ensures obsT sealed j' w' (cfg (Throw x) (f0 :: k0) s0) (cfg (Throw x) (f :: kk) s)) =
  kRel_mono sealed dd vv j j' w w' k0 kk;
  assert (obsT sealed j' w' (cfg (Throw x) k0 s0) (cfg (Throw x) kk s));
  obsT_back sealed j' w' (cfg (Throw x) (f0 :: k0) s0) (cfg (Throw x) k0 s0) (cfg (Throw x) (f :: kk) s) (cfg (Throw x) kk s)
#pop-options

(* What KRef gives, at index j' and world w'', under a continuation related in the family of a
   larger index k. *)
#push-options "--z3rlimit 120 --fuel 1 --ifuel 1"
let kRef_at (sealed : list name) (dd : list (name & fundef)) (g : list name) (e0 e : expr) (k j j' : nat)
  (w' w'' : world) (rho0 rho : lenv) (k0 kk : list frame) (s0 s : store)
  : Lemma (requires kRef sealed dd g e0 e /\ j' <= j /\ j <= k /\ wext w' w'' /\
                    envRel_with (vRel sealed dd j') w'' g rho0 rho /\
                    kRel_with sealed dd (vRelF sealed dd k) j w' k0 kk /\ sRel_with dd (vRelF sealed dd k j') w'' s0 s)
          (ensures obsT sealed j' w'' (cfg (Eval rho0 e0) k0 s0) (cfg (Eval rho e) kk s)) =
  assert (eRel sealed dd j' w'' rho0 e0 rho e);
  kRel_mono sealed dd (vRelF sealed dd k) j j' w' w'' k0 kk;
  family_down sealed dd k j';
  kRel_with_ext sealed dd (vRelF sealed dd k) (vRelF sealed dd j') j' w'' k0 kk;
  sRel_with_iff dd (vRelF sealed dd k j') (vRelF sealed dd j' j') w'' s0 s;
  wext_refl w''
#pop-options

(* ---------- the let frame ---------- *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let kRel_let (sealed : list name) (dd : list (name & fundef)) (k j : nat) (w w' : world) (g : list name) (x : name)
  (b0 b : expr) (rho0 rho : lenv) (k0 kk : list frame)
  : Lemma (requires j <= k /\ wext w w' /\ envRel_with (vRel sealed dd k) w g rho0 rho /\ kRef sealed dd (x :: g) b0 b /\
                    kRel_with sealed dd (vRelF sealed dd k) j w' k0 kk)
          (ensures kRel_with sealed dd (vRelF sealed dd k) j w' (KLet x b0 rho0 :: k0) (KLet x b rho :: kk)) =
  introduce forall (j' : nat). j' <= j ==> (forall w''. wext w' w'' ==>
   ((forall v0 v s0 s. vRelF sealed dd k j' w'' v0 v ==> sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Ret v0) (KLet x b0 rho0 :: k0) s0) (cfg (Ret v) (KLet x b rho :: kk) s)) /\
    (forall x' s0 s. sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Throw x') (KLet x b0 rho0 :: k0) s0) (cfg (Throw x') (KLet x b rho :: kk) s))))
  with introduce _ ==> _ with introduce forall w''. _ with introduce _ ==> _ with begin
    wext_trans w w' w'';
    let thr (x' : exn) (s0 s : store)
      : Lemma (requires sRel_with dd (vRelF sealed dd k j') w'' s0 s)
              (ensures obsT sealed j' w'' (cfg (Throw x') (KLet x b0 rho0 :: k0) s0) (cfg (Throw x') (KLet x b rho :: kk) s)) =
      throw_frame sealed dd (vRelF sealed dd k) j j' w' w'' (KLet x b0 rho0) (KLet x b rho) k0 kk x' s0 s in
    introduce forall x' s0 s. sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Throw x') (KLet x b0 rho0 :: k0) s0) (cfg (Throw x') (KLet x b rho :: kk) s)
    with introduce _ ==> _ with thr x' s0 s;
    introduce forall v0 v s0 s. vRelF sealed dd k j' w'' v0 v ==> sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Ret v0) (KLet x b0 rho0 :: k0) s0) (cfg (Ret v) (KLet x b rho :: kk) s)
    with introduce _ ==> _ with introduce _ ==> _ with begin
      vRelF_index sealed dd k j' w'' v0 v;
      envRel_mono sealed dd k j' w w'' g rho0 rho;
      envRel_cons sealed dd j' w'' g rho0 rho x v0 v;
      kRef_at sealed dd (x :: g) b0 b k j j' w' w'' ((x, v0) :: rho0) ((x, v) :: rho) k0 kk s0 s;
      introduce forall (x' : exn). obsT sealed j' w'' (cfg (Throw x') (KLet x b0 rho0 :: k0) s0) (cfg (Throw x') (KLet x b rho :: kk) s)
      with thr x' s0 s;
      obsT_back sealed j' w'' (cfg (Ret v0) (KLet x b0 rho0 :: k0) s0) (cfg (Eval ((x, v0) :: rho0) b0) k0 s0)
        (cfg (Ret v) (KLet x b rho :: kk) s) (cfg (Eval ((x, v) :: rho) b) kk s)
    end
  end
#pop-options

(* ---------- the if frame ---------- *)
let vRel_bool (sealed : list name) (dd : list (name & fundef)) (j : nat) (w : world) (v0 v : value)
  : Lemma (requires vRel sealed dd j w v0 v)
          (ensures (VBool? v0 <==> VBool? v) /\ (VBool? v ==> v0 == v)) =
  vRel_unfold sealed dd j w v0 v

#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let kRel_if (sealed : list name) (dd : list (name & fundef)) (k j : nat) (w w' : world) (g : list name)
  (a0 a b0 b : expr) (rho0 rho : lenv) (k0 kk : list frame)
  : Lemma (requires j <= k /\ wext w w' /\ envRel_with (vRel sealed dd k) w g rho0 rho /\
                    kRef sealed dd g a0 a /\ kRef sealed dd g b0 b /\ kRel_with sealed dd (vRelF sealed dd k) j w' k0 kk)
          (ensures kRel_with sealed dd (vRelF sealed dd k) j w' (KIf a0 b0 rho0 :: k0) (KIf a b rho :: kk)) =
  introduce forall (j' : nat). j' <= j ==> (forall w''. wext w' w'' ==>
   ((forall v0 v s0 s. vRelF sealed dd k j' w'' v0 v ==> sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Ret v0) (KIf a0 b0 rho0 :: k0) s0) (cfg (Ret v) (KIf a b rho :: kk) s)) /\
    (forall x' s0 s. sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Throw x') (KIf a0 b0 rho0 :: k0) s0) (cfg (Throw x') (KIf a b rho :: kk) s))))
  with introduce _ ==> _ with introduce forall w''. _ with introduce _ ==> _ with begin
    wext_trans w w' w'';
    let thr (x' : exn) (s0 s : store)
      : Lemma (requires sRel_with dd (vRelF sealed dd k j') w'' s0 s)
              (ensures obsT sealed j' w'' (cfg (Throw x') (KIf a0 b0 rho0 :: k0) s0) (cfg (Throw x') (KIf a b rho :: kk) s)) =
      throw_frame sealed dd (vRelF sealed dd k) j j' w' w'' (KIf a0 b0 rho0) (KIf a b rho) k0 kk x' s0 s in
    introduce forall x' s0 s. sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Throw x') (KIf a0 b0 rho0 :: k0) s0) (cfg (Throw x') (KIf a b rho :: kk) s)
    with introduce _ ==> _ with thr x' s0 s;
    introduce forall v0 v s0 s. vRelF sealed dd k j' w'' v0 v ==> sRel_with dd (vRelF sealed dd k j') w'' s0 s ==>
       obsT sealed j' w'' (cfg (Ret v0) (KIf a0 b0 rho0 :: k0) s0) (cfg (Ret v) (KIf a b rho :: kk) s)
    with introduce _ ==> _ with introduce _ ==> _ with begin
      vRelF_index sealed dd k j' w'' v0 v;
      vRel_bool sealed dd j' w'' v0 v;
      envRel_mono sealed dd k j' w w'' g rho0 rho;
      introduce forall (x' : exn). obsT sealed j' w'' (cfg (Throw x') (KIf a0 b0 rho0 :: k0) s0) (cfg (Throw x') (KIf a b rho :: kk) s)
      with thr x' s0 s;
      let c0 = cfg (Ret v0) (KIf a0 b0 rho0 :: k0) s0 in
      let c = cfg (Ret v) (KIf a b rho :: kk) s in
      match v with
      | VBool true ->
        kRef_at sealed dd g b0 b k j j' w' w'' rho0 rho k0 kk s0 s;
        obsT_back sealed j' w'' c0 (cfg (Eval rho0 b0) k0 s0) c (cfg (Eval rho b) kk s)
      | VBool false ->
        kRef_at sealed dd g b0 b k j j' w' w'' rho0 rho k0 kk s0 s;
        obsT_back sealed j' w'' c0 (cfg (Eval rho0 b0) k0 s0) c (cfg (Eval rho b) kk s)
      | _ ->
        kRel_mono sealed dd (vRelF sealed dd k) j j' w' w'' k0 kk;
        assert (obsT sealed j' w'' (cfg (Throw XNotBoolean) k0 s0) (cfg (Throw XNotBoolean) kk s));
        obsT_back sealed j' w'' c0 (cfg (Throw XNotBoolean) k0 s0) c (cfg (Throw XNotBoolean) kk s)
    end
  end
#pop-options

(* ---------- compat_let and compat_if ---------- *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let compat_let (sealed : list name) (dd : list (name & fundef)) (g : list name) (x : name) (a0 a b0 b : expr)
  : Lemma (requires kRef sealed dd g a0 a /\ kRef sealed dd (x :: g) b0 b)
          (ensures kRef sealed dd g (ELet x a0 b0) (ELet x a b)) =
  introduce forall (k : nat) w rho0 rho. wf_world w ==> envRel_with (vRel sealed dd k) w g rho0 rho ==>
    eRel sealed dd k w rho0 (ELet x a0 b0) rho (ELet x a b)
  with introduce _ ==> _ with introduce _ ==> _ with
  introduce forall (j : nat). j <= k ==> (forall w'. wext w w' ==> (forall k0 kk. kRel_with sealed dd (vRelF sealed dd k) j w' k0 kk ==>
   (forall s0 s. sRel_with dd (vRelF sealed dd k j) w' s0 s ==>
     obsT sealed j w' (cfg (Eval rho0 (ELet x a0 b0)) k0 s0) (cfg (Eval rho (ELet x a b)) kk s))))
  with introduce _ ==> _ with introduce forall w'. _ with introduce _ ==> _ with
  introduce forall k0 kk. _ with introduce _ ==> _ with
  introduce forall s0 s. _ with introduce _ ==> _ with begin
    kRel_let sealed dd k j w w' g x b0 b rho0 rho k0 kk;
    envRel_mono sealed dd k j w w' g rho0 rho;
    wext_refl w';
    kRef_at sealed dd g a0 a k j j w' w' rho0 rho (KLet x b0 rho0 :: k0) (KLet x b rho :: kk) s0 s;
    assert (forall (x' : exn). obsT sealed j w' (cfg (Throw x') k0 s0) (cfg (Throw x') kk s));
    obsT_back sealed j w' (cfg (Eval rho0 (ELet x a0 b0)) k0 s0) (cfg (Eval rho0 a0) (KLet x b0 rho0 :: k0) s0)
      (cfg (Eval rho (ELet x a b)) kk s) (cfg (Eval rho a) (KLet x b rho :: kk) s)
  end

let compat_if (sealed : list name) (dd : list (name & fundef)) (g : list name) (c0 c a0 a b0 b : expr)
  : Lemma (requires kRef sealed dd g c0 c /\ kRef sealed dd g a0 a /\ kRef sealed dd g b0 b)
          (ensures kRef sealed dd g (EIf c0 a0 b0) (EIf c a b)) =
  introduce forall (k : nat) w rho0 rho. wf_world w ==> envRel_with (vRel sealed dd k) w g rho0 rho ==>
    eRel sealed dd k w rho0 (EIf c0 a0 b0) rho (EIf c a b)
  with introduce _ ==> _ with introduce _ ==> _ with
  introduce forall (j : nat). j <= k ==> (forall w'. wext w w' ==> (forall k0 kk. kRel_with sealed dd (vRelF sealed dd k) j w' k0 kk ==>
   (forall s0 s. sRel_with dd (vRelF sealed dd k j) w' s0 s ==>
     obsT sealed j w' (cfg (Eval rho0 (EIf c0 a0 b0)) k0 s0) (cfg (Eval rho (EIf c a b)) kk s))))
  with introduce _ ==> _ with introduce forall w'. _ with introduce _ ==> _ with
  introduce forall k0 kk. _ with introduce _ ==> _ with
  introduce forall s0 s. _ with introduce _ ==> _ with begin
    kRel_if sealed dd k j w w' g a0 a b0 b rho0 rho k0 kk;
    envRel_mono sealed dd k j w w' g rho0 rho;
    wext_refl w';
    kRef_at sealed dd g c0 c k j j w' w' rho0 rho (KIf a0 b0 rho0 :: k0) (KIf a b rho :: kk) s0 s;
    assert (forall (x' : exn). obsT sealed j w' (cfg (Throw x') k0 s0) (cfg (Throw x') kk s));
    obsT_back sealed j w' (cfg (Eval rho0 (EIf c0 a0 b0)) k0 s0) (cfg (Eval rho0 c0) (KIf a0 b0 rho0 :: k0) s0)
      (cfg (Eval rho (EIf c a b)) kk s) (cfg (Eval rho c) (KIf a b rho :: kk) s)
  end
#pop-options

(* Rocq: compat_let_statement and compat_if_statement. *)
let compat_let_statement (sealed : list name) (dd : list (name & fundef)) : Lemma
  (forall g x a0 a b0 b. kRef sealed dd g a0 a ==> kRef sealed dd (x :: g) b0 b ==> kRef sealed dd g (ELet x a0 b0) (ELet x a b)) =
  introduce forall g x a0 a b0 b. kRef sealed dd g a0 a ==> kRef sealed dd (x :: g) b0 b ==> kRef sealed dd g (ELet x a0 b0) (ELet x a b)
  with introduce _ ==> _ with introduce _ ==> _ with compat_let sealed dd g x a0 a b0 b
let compat_if_statement (sealed : list name) (dd : list (name & fundef)) : Lemma
  (forall g c0 c a0 a b0 b. kRef sealed dd g c0 c ==> kRef sealed dd g a0 a ==> kRef sealed dd g b0 b ==>
     kRef sealed dd g (EIf c0 a0 b0) (EIf c a b)) =
  introduce forall g c0 c a0 a b0 b. kRef sealed dd g c0 c ==> kRef sealed dd g a0 a ==> kRef sealed dd g b0 b ==>
     kRef sealed dd g (EIf c0 a0 b0) (EIf c a b)
  with introduce _ ==> _ with introduce _ ==> _ with introduce _ ==> _ with compat_if sealed dd g c0 c a0 a b0 b
