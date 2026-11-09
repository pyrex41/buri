(* Port of rocq/JitLowerEquiv.v at branch pass/equiv (670d29d): the step-indexed Kripke logical
   relation KRef for the lowerer's front passes, its definitions, the premise checks, the ground
   relation, and the implications Rocq proves from the (unproved) fundamental property.
   Encoding:
   - Section variables `sealed` and `D` are explicit parameters (`sealed`, `dd`).
   - Rocq Props over derivations (runs, star) quantify over F* derivation values, or use
     `inhabited`; the relations themselves (GVal, VBody, ObsT, KRel, ERel, KRef) are prop-valued
     recursive functions, as in Rocq.
   - Fixpoints with nested list recursion (GVal, VBody, names, binders, scoped) are mutual
     functions with a list companion.
   - Every Rocq `..._statement : Prop` that Rocq does not prove is in Buri.Unfinished form here:
     a `prop` definition, never assumed; implications take it as a hypothesis. *)
module Buri.JitLowerEquiv
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.KLPort
open Buri.JitProfile
open Buri.JitLowerRel
open Buri.JitLowerKont
open Buri.JitLowerPrim
open Buri.JitLowerStep
open Buri.JitLowerThm
open Buri.JitLowerCheck
module B = Buri.JitBytecode

(* ---------- runs ---------- *)
noeq type runs (sealed : list name) : nat -> config -> trace -> config -> Type0 =
  | Runs_0 : c:config -> runs sealed 0 c [] c
  | Runs_S : n:nat -> c:config -> l:label -> c1:config -> t:trace -> c2:config ->
      step_r (rr sealed) pr c l c1 -> runs sealed n c1 t c2 -> runs sealed (n + 1) c (app (trace_of l) t) c2

let srun (sealed : list name) (c : config) (t : trace) (c' : config) : prop =
  inhabited (star (step_r (rr sealed) pr) c t c')

(* ---------- worlds ---------- *)
type world = list (nat & nat)
let wf_world (w : world) : prop = nodup_l (map fst w) /\ nodup_l (map snd w)
let incl (w w' : world) : prop = forall (p : nat & nat). mem_l p w ==> mem_l p w'
let wext (w w' : world) : prop = incl w w' /\ wf_world w'

let same_id (w : world) (r0 r : lenv) : prop =
  match closure_id r0, closure_id r with
  | Some l0, Some l -> mem_l (l0, l) w
  | None, None -> True
  | _, _ -> False

let storeHas (dd : list (name & fundef)) (s : store) : prop =
  forall f d. mem_l (f, d) dd ==> lookup f s.gfuns == Some d

(* ---------- the ground relation ---------- *)
let rec gVal (w : world) (v0 v : value) : Tot prop (decreases v0) =
  match v0, v with
  | VNum a, VNum b -> a == b
  | VSym a, VSym b -> a == b
  | VBool a, VBool b -> a == b
  | VStr a, VStr b -> a == b
  | VNil, VNil -> True
  | VCons a0 d0, VCons a d -> gVal w a0 a /\ gVal w d0 d
  | VVec l0, VVec l -> mem_l (l0, l) w
  | VStream h0, VStream h -> h0 == h
  | VLam _ _ r0, VLam _ _ r -> same_id w r0 r
  | VFrozen _ r0, VFrozen _ r -> same_id w r0 r
  | VPartial f0 as0, VPartial f as1 -> f0 == f /\ gVal_list w as0 as1
  | VExn x0, VExn x -> x0 == x
  | _, _ -> False
and gVal_list (w : world) (l0 l : list value) : Tot prop (decreases l0) =
  match l0, l with
  | [], [] -> True
  | x0 :: r0, x :: r -> gVal w x0 x /\ gVal_list w r0 r
  | _, _ -> False

(* Pairs of global bindings, related: a named predicate (not a lambda), so that SMT can match the
   statements that use it. *)
let glob_rel (v1 : world -> value -> value -> prop) (w : world) (p0 p : name & value) : prop =
  fst p0 == fst p /\ v1 w (snd p0) (snd p)

let gStore (w : world) (s0 s : store) : prop =
  s0.gfuns == s.gfuns /\
  forall2_l (glob_rel gVal w) s0.gvals s.gvals /\
  (forall (l0 l : nat). mem_l (l0, l) w ==> (exists c0 c. nth_error s0.heap l0 == Some c0 /\
     nth_error s.heap l == Some c /\ forall2_l (gVal w) c0 c))

(* ---------- observation ---------- *)
let obsT (sealed : list name) (k : nat) (w : world) (c0 c : config) : prop =
  forall (n : nat) (t : trace) (c' : config). n < k ==> (forall (h : runs sealed n c t c').
   (forall v s. c' == cfg (Ret v) [] s ==> (exists v0 s0 w'.
      srun sealed c0 t (cfg (Ret v0) [] s0) /\ wext w w' /\ gVal w' v0 v /\ gStore w' s0 s)) /\
   (forall x s. c' == cfg (Throw x) [] s ==> (exists s0 w'.
      srun sealed c0 t (cfg (Throw x) [] s0) /\ wext w w' /\ gStore w' s0 s)) /\
   (forall why. next_r (rr sealed) pr c' == MWrong why ==> (exists c0' why0.
      srun sealed c0 t c0' /\ next_r (rr sealed) pr c0' == MWrong why0)))

(* ---------- the logical relation, generic in the value relation at lower indices ---------- *)
type vrelt = nat -> world -> value -> value -> prop

let sRel_with (dd : list (name & fundef)) (v1 : world -> value -> value -> prop) (w : world) (s0 s : store) : prop =
  wf_world w /\ storeHas dd s0 /\ storeHas dd s /\ s0.gfuns == s.gfuns /\
  forall2_l (glob_rel v1 w) s0.gvals s.gvals /\
  (forall (l0 l : nat). mem_l (l0, l) w ==> (exists c0 c. nth_error s0.heap l0 == Some c0 /\
     nth_error s.heap l == Some c /\ forall2_l (v1 w) c0 c))

let envRel_with (v1 : world -> value -> value -> prop) (w : world) (g : list name) (rho0 rho : lenv) : prop =
  forall x. mem_l x g ==> (exists v0 v. lookup x rho0 == Some v0 /\ lookup x rho == Some v /\ v1 w v0 v)

let kRel_with (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w : world)
  (k0 kk : list frame) : prop =
  forall (j : nat). j <= k ==> (forall w'. wext w w' ==>
   ((forall v0 v s0 s. vv j w' v0 v ==> sRel_with dd (vv j) w' s0 s ==>
       obsT sealed j w' (cfg (Ret v0) k0 s0) (cfg (Ret v) kk s)) /\
    (forall x s0 s. sRel_with dd (vv j) w' s0 s ==>
       obsT sealed j w' (cfg (Throw x) k0 s0) (cfg (Throw x) kk s))))

let eRel_with (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w : world)
  (rho0 : lenv) (e0 : expr) (rho : lenv) (e : expr) : prop =
  forall (j : nat). j <= k ==> (forall w'. wext w w' ==> (forall k0 kk. kRel_with sealed dd vv j w' k0 kk ==>
   (forall s0 s. sRel_with dd (vv j) w' s0 s ==>
     obsT sealed j w' (cfg (Eval rho0 e0) k0 s0) (cfg (Eval rho e) kk s))))

let rec vBody (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w : world)
  (v0 v : value) : Tot prop (decreases v0) =
  match v0, v with
  | VNum a, VNum b -> a == b
  | VSym a, VSym b -> a == b
  | VBool a, VBool b -> a == b
  | VStr a, VStr b -> a == b
  | VNil, VNil -> True
  | VCons a0 d0, VCons a d -> vBody sealed dd vv k w a0 a /\ vBody sealed dd vv k w d0 d
  | VVec l0, VVec l -> mem_l (l0, l) w
  | VStream h0, VStream h -> h0 == h
  | VLam x0 b0 r0, VLam x b r -> same_id w r0 r /\
      (forall (j : nat). j < k ==> (forall w'. wext w w' ==> (forall a0 a. vv j w' a0 a ==>
        eRel_with sealed dd vv j w' ((x0, a0) :: r0) b0 ((x, a) :: r) b)))
  | VFrozen b0 r0, VFrozen b r -> same_id w r0 r /\
      (forall (j : nat). j < k ==> (forall w'. wext w w' ==> eRel_with sealed dd vv j w' r0 b0 r b))
  | VPartial f0 as0, VPartial f as1 -> f0 == f /\ vBody_list sealed dd vv k w as0 as1
  | VExn x0, VExn x -> x0 == x
  | _, _ -> False
and vBody_list (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w : world)
  (l0 l : list value) : Tot prop (decreases l0) =
  match l0, l with
  | [], [] -> True
  | x0 :: r0, x :: r -> vBody sealed dd vv k w x0 x /\ vBody_list sealed dd vv k w r0 r
  | _, _ -> False

(* The value relation below index 0 (Rocq: fun _ _ _ _ => False), named so statements can refer to it. *)
let bottom_rel : vrelt = fun _ _ _ _ -> False

(* The relations at every index up to k; vRelF k j is the value relation at j for j <= k. *)
let rec vRelF (sealed : list name) (dd : list (name & fundef)) (k : nat) : Tot vrelt (decreases k) =
  if k = 0 then (fun _ -> vBody sealed dd bottom_rel 0)
  else (fun j -> if j <= k - 1 then vRelF sealed dd (k - 1) j else vBody sealed dd (vRelF sealed dd (k - 1)) k)

let vRel sealed dd (k : nat) : world -> value -> value -> prop = vRelF sealed dd k k
let sRel sealed dd (k : nat) : world -> store -> store -> prop = sRel_with dd (vRel sealed dd k)
let kRel sealed dd (k : nat) : world -> list frame -> list frame -> prop = kRel_with sealed dd (vRelF sealed dd k) k
let eRel sealed dd (k : nat) : world -> lenv -> expr -> lenv -> expr -> prop = eRel_with sealed dd (vRelF sealed dd k) k

(* ---------- KRef ---------- *)
let kRef sealed dd (g : list name) (e0 e : expr) : prop =
  forall (k : nat) w rho0 rho. wf_world w ==> envRel_with (vRel sealed dd k) w g rho0 rho ==>
    eRel sealed dd k w rho0 e0 rho e

(* ---------- premises, as decidable checks ---------- *)
let ns_stage0 : name = of_string "stage0.lower."
let ns_runtime : name = of_string "shen-jit.lower."
let lowerer_prefixes (ns : name) : list name =
  map (fun p -> app ns (of_string p)) ["else"; "exception"; "arg"; "head"; "partial"]
let lowerer_fixed (ns : name) : list name = [app ns (of_string "inlining"); id_key]

let rec prefixb (p t : text) : bool = match p, t with
  | [], _ -> true
  | a :: p, b :: t -> a = b && prefixb p t
  | _ :: _, [] -> false
let digitb (c : nat) : bool = 48 <= c && c <= 57
let fresh_shape (p x : name) : bool =
  prefixb p x && not (length x = length p) && forallb digitb (skipn (length p) x)
let reserved (ns x : name) : bool =
  existsb (fun p -> fresh_shape p x) (lowerer_prefixes ns) || existsb (text_eqb x) (lowerer_fixed ns)

let rec names (e : expr) : Tot (list name) (decreases e) = match e with
  | ENum _ | EStr _ | EBool _ | ENil -> []
  | ESym s -> [s]
  | EVar x -> [x]
  | ELam x b -> x :: names b
  | ELet x a b -> x :: app (names a) (names b)
  | EIf c a b -> app (names c) (app (names a) (names b))
  | EAnd a b | EOr a b | ETrap a b -> app (names a) (names b)
  | ECond cl -> names_cl cl
  | EFreeze b | EType b -> names b
  | EDefun f ps b -> f :: app ps (names b)
  | EApp h args -> app (names h) (names_l args)
  | ECall f args -> f :: names_l args
and names_cl (l : list (expr & expr)) : Tot (list name) (decreases l) = match l with
  | [] -> [] | (c, b) :: l' -> app (names c) (app (names b) (names_cl l'))
and names_l (l : list expr) : Tot (list name) (decreases l) = match l with
  | [] -> [] | a :: l' -> app (names a) (names_l l')

let d_bodies (dd : list (name & fundef)) : list expr =
  flat_map (fun (p : name & fundef) -> match snd p with FUser _ b -> [b] | FPrim _ -> []) dd
let fresh_ok (ns : name) (es : list expr) : bool =
  forallb (fun e -> forallb (fun x -> not (reserved ns x)) (names e)) es

let rec binders (e : expr) : Tot (list name) (decreases e) = match e with
  | ELam x b -> x :: binders b
  | ELet x a b -> x :: app (binders a) (binders b)
  | EIf c a b -> app (binders c) (app (binders a) (binders b))
  | EAnd a b | EOr a b | ETrap a b -> app (binders a) (binders b)
  | ECond cl -> binders_cl cl
  | EFreeze b | EType b -> binders b
  | EDefun _ ps b -> app ps (binders b)
  | EApp h args -> app (binders h) (binders_l args)
  | ECall _ args -> binders_l args
  | _ -> []
and binders_cl (l : list (expr & expr)) : Tot (list name) (decreases l) = match l with
  | [] -> [] | (c, b) :: l' -> app (binders c) (app (binders b) (binders_cl l'))
and binders_l (l : list expr) : Tot (list name) (decreases l) = match l with
  | [] -> [] | a :: l' -> app (binders a) (binders_l l')
let no_keyword_binders (e : expr) : bool = forallb (fun x -> not (keyword x)) (binders e)

let d_wf (sealed : list name) (dd : list (name & fundef)) : prop =
  forall_l (fun (p : name & fundef) -> mem_l (fst p) sealed) dd /\ nodup_l (map fst dd)

let d_compiled (dd : list (name & fundef)) (cs : list (name & B.code)) : bool =
  forallb (fun (p : name & fundef) -> match snd p with
    | FUser ps b -> (match lookup (fst p) cs with Some c -> check_fn c ps b | None -> false)
    | FPrim _ -> true) dd

let rec scoped (g : list name) (e : expr) : Tot bool (decreases e) = match e with
  | EVar x -> bound g x
  | ELam x b -> scoped (x :: g) b
  | ELet x a b -> scoped g a && scoped (x :: g) b
  | EIf c a b -> scoped g c && scoped g a && scoped g b
  | EAnd a b | EOr a b | ETrap a b -> scoped g a && scoped g b
  | ECond cl -> scoped_cl g cl
  | EFreeze b | EType b -> scoped g b
  | EDefun _ ps b -> scoped ps b
  | EApp h args -> scoped g h && scoped_l g args
  | ECall _ args -> scoped_l g args
  | _ -> true
and scoped_cl (g : list name) (l : list (expr & expr)) : Tot bool (decreases l) = match l with
  | [] -> true | (c, b) :: l' -> scoped g c && scoped g b && scoped_cl g l'
and scoped_l (g : list name) (l : list expr) : Tot bool (decreases l) = match l with
  | [] -> true | a :: l' -> scoped g a && scoped_l g l'

let rec seq (start len : nat) : Tot (list nat) (decreases len) = if len = 0 then [] else start :: seq (start + 1) (len - 1)
let id_world (s : store) : world = map (fun (l : nat) -> (l, l)) (seq 0 (length s.heap))

(* ======================= proofs ======================= *)
(* --- premise specifications --- *)
let rec forallb_spec (#a : Type) (f : a -> bool) (l : list a)
  : Lemma (forallb f l = true <==> (forall x. mem_l x l ==> f x = true)) =
  match l with [] -> () | _ :: r -> forallb_spec f r

let fresh_ok_spec (ns : name) (es : list expr)
  : Lemma (fresh_ok ns es = true <==> (forall e x. mem_l e es ==> mem_l x (names e) ==> reserved ns x = false)) =
  forallb_spec (fun e -> forallb (fun x -> not (reserved ns x)) (names e)) es;
  introduce forall e. forallb (fun x -> not (reserved ns x)) (names e) = true <==>
    (forall x. mem_l x (names e) ==> reserved ns x = false)
  with forallb_spec (fun x -> not (reserved ns x)) (names e)

let no_keyword_binders_spec (e : expr)
  : Lemma (no_keyword_binders e = true <==> (forall x. mem_l x (binders e) ==> keyword x = false)) =
  forallb_spec (fun x -> not (keyword x)) (binders e)

let d_compiled_spec (dd : list (name & fundef)) (cs : list (name & B.code))
  : Lemma (requires d_compiled dd cs = true)
          (ensures forall f ps b. mem_l (f, FUser ps b) dd ==> (exists c. lookup f cs == Some c /\ compFn c ps b)) =
  let p (q : name & fundef) : bool = (match snd q with
    | FUser ps b -> (match lookup (fst q) cs with Some c -> check_fn c ps b | None -> false)
    | FPrim _ -> true) in
  forallb_spec p dd;
  introduce forall f ps b. mem_l (f, FUser ps b) dd ==> (exists c. lookup f cs == Some c /\ compFn c ps b)
  with introduce _ ==> _ with begin
    assert (p (f, FUser ps b) = true);
    match lookup f cs with Some c -> check_fn_sound c ps b
  end

(* --- runs --- *)
let rec runs_srun (#sealed : list name) (#n : nat) (#c : config) (#t : trace) (#c' : config) (h : runs sealed n c t c')
  : Tot (star (step_r (rr sealed) pr) c t c') (decreases h) =
  match h with
  | Runs_0 _ -> Star_refl c
  | Runs_S n1 _ l c1 t1 _ st rest -> Star_step c l c1 t1 c' st (runs_srun rest)

let rec srun_runs (#sealed : list name) (#c : config) (#t : trace) (#c' : config) (h : star (step_r (rr sealed) pr) c t c')
  : Tot (n : nat & runs sealed n c t c') (decreases h) =
  match h with
  | Star_refl _ -> (| 0, Runs_0 c |)
  | Star_step _ l c1 t1 _ st rest -> let (| n, r |) = srun_runs rest in (| n + 1, Runs_S n c l c1 t1 c' st r |)

let rec star_nil_sstar (#sealed : list name) (#c #c' : config) (h : star (step_r (rr sealed) pr) c [] c')
  : Tot (sstar sealed c c') (decreases h) =
  match h with
  | Star_refl _ -> SS_refl c
  | Star_step _ l c1 t1 _ st rest ->
    (match l with Tau -> SS_step c c1 c' st (star_nil_sstar rest))
let rec sstar_star_nil (#sealed : list name) (#c #c' : config) (h : sstar sealed c c')
  : Tot (star (step_r (rr sealed) pr) c [] c') (decreases h) =
  match h with
  | SS_refl _ -> Star_refl c
  | SS_step _ c1 _ st rest -> Star_step c Tau c1 [] c' st (sstar_star_nil rest)

let srun_nil_sstar (sealed : list name) (c c' : config)
  : Lemma (srun sealed c [] c' <==> inhabited (sstar sealed c c')) =
  introduce srun sealed c [] c' ==> inhabited (sstar sealed c c')
  with eliminate exists (h : star (step_r (rr sealed) pr) c [] c'). True
       with (let _ = star_nil_sstar h in ());
  introduce inhabited (sstar sealed c c') ==> srun sealed c [] c'
  with eliminate exists (h : sstar sealed c c'). True
       with (let _ = sstar_star_nil h in ())

let step_from_ret_top (sealed : list name) (v : value) (s : store) (l : label) (c1 : config)
  (h : step_r (rr sealed) pr (cfg (Ret v) [] s) l c1)
  : Lemma (l == Tau /\ (exists x r. (rr sealed).resource_exn r == Some x /\ c1 == cfg (Throw x) [] s)) =
  match h with
  | Step_r_resource _ _ _ _ _ -> ()

let no_step_from_throw_top (sealed : list name) (x : exn) (s : store) (l : label) (c1 : config)
  (h : step_r (rr sealed) pr (cfg (Throw x) [] s) l c1) : Lemma False =
  match h with
  | Step_r_tau _ _ _ -> ()

(* --- worlds --- *)
let wext_refl (w : world) : Lemma (requires wf_world w) (ensures wext w w) = ()

let compose_world (w1 w2 : world) : world =
  flat_map (fun (p : nat & nat) -> map (fun (q : nat & nat) -> (fst p, snd q))
    (filter (fun (q : nat & nat) -> snd p = fst q) w2)) w1

let rec mem_app (#a : Type) (x : a) (l1 l2 : list a)
  : Lemma (mem_l x (app l1 l2) <==> mem_l x l1 \/ mem_l x l2) =
  match l1 with [] -> () | _ :: r -> mem_app x r l2
let rec mem_map (#a #b : Type) (f : a -> b) (y : b) (l : list a)
  : Lemma (mem_l y (map f l) <==> (exists x. mem_l x l /\ y == f x)) =
  match l with [] -> () | _ :: r -> mem_map f y r
let rec mem_filter (#a : Type) (f : a -> bool) (x : a) (l : list a)
  : Lemma (mem_l x (filter f l) <==> mem_l x l /\ f x = true) =
  match l with [] -> () | _ :: r -> mem_filter f x r
let rec mem_flat_map (#a #b : Type) (f : a -> list b) (y : b) (l : list a)
  : Lemma (mem_l y (flat_map f l) <==> (exists x. mem_l x l /\ mem_l y (f x))) =
  match l with [] -> () | x :: r -> mem_app y (f x) (flat_map f r); mem_flat_map f y r

let compose_inner (w2 : world) (p : nat & nat) : list (nat & nat) =
  map (fun (q : nat & nat) -> (fst p, snd q)) (filter (fun (q : nat & nat) -> snd p = fst q) w2)

let compose_world_eq (w1 w2 : world) : Lemma (compose_world w1 w2 == flat_map (compose_inner w2) w1) =
  assert (compose_world w1 w2 == flat_map (compose_inner w2) w1) by (FStar.Tactics.V2.trefl ())

let mem_compose (w1 w2 : world) (a c : nat)
  : Lemma (mem_l (a, c) (compose_world w1 w2) <==> (exists (b : nat). mem_l (a, b) w1 /\ mem_l (b, c) w2)) =
  compose_world_eq w1 w2;
  mem_flat_map (compose_inner w2) (a, c) w1;
  introduce forall (p : nat & nat). mem_l (a, c) (compose_inner w2 p) <==> (fst p == a /\ mem_l (snd p, c) w2)
  with begin
    mem_map (fun (q : nat & nat) -> (fst p, snd q)) (a, c) (filter (fun (q : nat & nat) -> snd p = fst q) w2);
    introduce forall (q : nat & nat). mem_l q (filter (fun (q : nat & nat) -> snd p = fst q) w2) <==>
      (mem_l q w2 /\ snd p = fst q)
    with mem_filter (fun (q : nat & nat) -> snd p = fst q) q w2
  end

let mem_map_fst (a : nat) (l : world) : Lemma (mem_l a (map fst l) <==> (exists (c : nat). mem_l (a, c) l)) =
  mem_map fst a l
let mem_map_snd (c : nat) (l : world) : Lemma (mem_l c (map snd l) <==> (exists (a : nat). mem_l (a, c) l)) =
  mem_map snd c l

let rec nodup_snd_uniq (w : world) (a a' b : nat)
  : Lemma (requires nodup_l (map snd w) /\ mem_l (a, b) w /\ mem_l (a', b) w) (ensures a == a') =
  match w with
  | (x, y) :: w' ->
    mem_map_snd b w';
    if (x, y) = (a, b) && (x, y) = (a', b) then ()
    else if (x, y) = (a, b) then ()
    else if (x, y) = (a', b) then ()
    else nodup_snd_uniq w' a a' b

let rec filter_small (w2 : world) (b : nat)
  : Lemma (requires nodup_l (map fst w2))
          (ensures filter (fun (q : nat & nat) -> b = fst q) w2 == [] \/
                   (exists (q : nat & nat). filter (fun (q : nat & nat) -> b = fst q) w2 == [q] /\ mem_l q w2 /\ fst q == b)) =
  match w2 with
  | [] -> ()
  | (x, y) :: w' ->
    filter_small w' b;
    if b = x then begin
      mem_map_fst b w';
      (match filter (fun (q : nat & nat) -> b = fst q) w' with
       | [] -> ()
       | q :: _ -> mem_filter (fun (q : nat & nat) -> b = fst q) q w')
    end

let compose_cons (p : nat & nat) (w1 w2 : world)
  : Lemma (compose_world (p :: w1) w2 == app (compose_inner w2 p) (compose_world w1 w2)) =
  compose_world_eq (p :: w1) w2; compose_world_eq w1 w2

#push-options "--z3rlimit 40"
let rec wf_compose (w1 w2 : world)
  : Lemma (requires wf_world w1 /\ wf_world w2) (ensures wf_world (compose_world w1 w2)) =
  match w1 with
  | [] -> compose_world_eq [] w2
  | p :: w1' ->
    wf_compose w1' w2;
    compose_cons p w1' w2;
    filter_small w2 (snd p);
    (match filter (fun (q : nat & nat) -> snd p = fst q) w2 with
     | [] -> ()
     | [q] ->
       assert (compose_inner w2 p == [(fst p, snd q)]);
       mem_filter (fun (q : nat & nat) -> snd p = fst q) q w2;
       mem_map_fst (fst p) (compose_world w1' w2);
       mem_map_snd (snd q) (compose_world w1' w2);
       mem_map_fst (fst p) w1';
       mem_map_snd (snd p) w1';
       introduce forall (c : nat). ~(mem_l (fst p, c) (compose_world w1' w2))
       with (mem_compose w1' w2 (fst p) c);
       introduce forall (a' : nat). ~(mem_l (a', snd q) (compose_world w1' w2))
       with begin
         mem_compose w1' w2 a' (snd q);
         introduce forall (b' : nat). ~(mem_l (a', b') w1' /\ mem_l (b', snd q) w2)
         with introduce (mem_l (a', b') w1' /\ mem_l (b', snd q) w2) ==> False
         with (nodup_snd_uniq w2 b' (snd p) (snd q))
       end)
#pop-options

let rec mem_seq (x start len : nat) : Lemma (mem_l x (seq start len) <==> start <= x /\ x < start + len) (decreases len) =
  if len = 0 then () else mem_seq x (start + 1) (len - 1)
let rec nodup_seq (start len : nat) : Lemma (ensures nodup_l (seq start len)) (decreases len) =
  if len = 0 then () else (mem_seq start (start + 1) (len - 1); nodup_seq (start + 1) (len - 1))
let rec map_fst_diag (l : list nat)
  : Lemma (map fst (map (fun (x : nat) -> (x, x)) l) == l /\ map snd (map (fun (x : nat) -> (x, x)) l) == l) =
  match l with [] -> () | _ :: r -> map_fst_diag r

let id_world_wf (s : store) : Lemma (wf_world (id_world s)) =
  map_fst_diag (seq 0 (length s.heap)); nodup_seq 0 (length s.heap)
let id_world_mem (s : store) (a b : nat)
  : Lemma (mem_l (a, b) (id_world s) <==> a == b /\ a < length s.heap) =
  mem_map (fun (x : nat) -> (x, x)) (a, b) (seq 0 (length s.heap));
  mem_seq a 0 (length s.heap)

let wext_compose_id (s : store) (w1 w2 : world)
  : Lemma (requires wext (id_world s) w1 /\ wext (id_world s) w2) (ensures wext (id_world s) (compose_world w1 w2)) =
  wf_compose w1 w2;
  introduce forall (p : nat & nat). mem_l p (id_world s) ==> mem_l p (compose_world w1 w2)
  with introduce _ ==> _ with begin
    id_world_mem s (fst p) (snd p);
    mem_compose w1 w2 (fst p) (snd p)
  end

(* --- the ground relation --- *)
let same_id_trans (w1 w2 : world) (r0 r1 r : lenv)
  : Lemma (requires same_id w1 r0 r1 /\ same_id w2 r1 r) (ensures same_id (compose_world w1 w2) r0 r) =
  match closure_id r0, closure_id r1, closure_id r with
  | Some a, Some b, Some c -> mem_compose w1 w2 a c
  | _ -> ()

let rec gVal_trans (w1 w2 : world) (a b c : value)
  : Lemma (requires gVal w1 a b /\ gVal w2 b c) (ensures gVal (compose_world w1 w2) a c) (decreases a) =
  match a, b, c with
  | VCons a1 a2, VCons b1 b2, VCons c1 c2 -> gVal_trans w1 w2 a1 b1 c1; gVal_trans w1 w2 a2 b2 c2
  | VVec x, VVec y, VVec z -> mem_compose w1 w2 x z
  | VLam _ _ r0, VLam _ _ r1, VLam _ _ r -> same_id_trans w1 w2 r0 r1 r
  | VFrozen _ r0, VFrozen _ r1, VFrozen _ r -> same_id_trans w1 w2 r0 r1 r
  | VPartial _ l0, VPartial _ l1, VPartial _ l -> gVal_list_trans w1 w2 l0 l1 l
  | _ -> ()
and gVal_list_trans (w1 w2 : world) (a b c : list value)
  : Lemma (requires gVal_list w1 a b /\ gVal_list w2 b c) (ensures gVal_list (compose_world w1 w2) a c) (decreases a) =
  match a, b, c with
  | x :: a', y :: b', z :: c' -> gVal_trans w1 w2 x y z; gVal_list_trans w1 w2 a' b' c'
  | _ -> ()

(* Rocq: GVal_trans_statement, which also says the composed world is well formed. *)
let gVal_trans_statement (w1 w2 : world) (a b c : value)
  : Lemma (requires wf_world w1 /\ wf_world w2 /\ gVal w1 a b /\ gVal w2 b c)
          (ensures gVal (compose_world w1 w2) a c /\ wf_world (compose_world w1 w2)) =
  gVal_trans w1 w2 a b c; wf_compose w1 w2

let rec forall2_cells_trans (w1 w2 : world) (a b c : list value)
  : Lemma (requires forall2_l (gVal w1) a b /\ forall2_l (gVal w2) b c)
          (ensures forall2_l (gVal (compose_world w1 w2)) a c) =
  match a, b, c with
  | x :: a', y :: b', z :: c' -> gVal_trans w1 w2 x y z; forall2_cells_trans w1 w2 a' b' c'
  | _ -> ()
let rec forall2_globals_trans (w1 w2 : world) (a b c : list (name & value))
  : Lemma (requires forall2_l (glob_rel gVal w1) a b /\ forall2_l (glob_rel gVal w2) b c)
          (ensures forall2_l (glob_rel gVal (compose_world w1 w2)) a c) =
  match a, b, c with
  | x :: a', y :: b', z :: c' -> gVal_trans w1 w2 (snd x) (snd y) (snd z); forall2_globals_trans w1 w2 a' b' c'
  | _ -> ()

let gStore_trans (w1 w2 : world) (s0 s1 s : store)
  : Lemma (requires wf_world w1 /\ wf_world w2 /\ gStore w1 s0 s1 /\ gStore w2 s1 s)
          (ensures gStore (compose_world w1 w2) s0 s) =
  forall2_globals_trans w1 w2 s0.gvals s1.gvals s.gvals;
  introduce forall (l0 l : nat). mem_l (l0, l) (compose_world w1 w2) ==> (exists c0 c. nth_error s0.heap l0 == Some c0 /\
     nth_error s.heap l == Some c /\ forall2_l (gVal (compose_world w1 w2)) c0 c)
  with introduce _ ==> _ with begin
    mem_compose w1 w2 l0 l;
    eliminate exists (b : nat). mem_l (l0, b) w1 /\ mem_l (b, l) w2
    with begin
      eliminate exists c0 c1. nth_error s0.heap l0 == Some c0 /\ nth_error s1.heap b == Some c1 /\ forall2_l (gVal w1) c0 c1
      with eliminate exists c1' c. nth_error s1.heap b == Some c1' /\ nth_error s.heap l == Some c /\ forall2_l (gVal w2) c1' c
      with forall2_cells_trans w1 w2 c0 c1 c
    end
  end

(* First-order values. *)
noeq type fo : value -> Type0 =
  | Fo_num : n:num -> fo (VNum n) | Fo_sym : x:name -> fo (VSym x) | Fo_bool : b:bool -> fo (VBool b)
  | Fo_str : t:text -> fo (VStr t) | Fo_nil : fo VNil | Fo_cons : a:value -> d:value -> fo a -> fo d -> fo (VCons a d)

let rec gVal_fo (w : world) (v0 v : value) (f : fo v) : Lemma (requires gVal w v0 v) (ensures v0 == v) (decreases f) =
  match f with
  | Fo_cons a d fa fd -> (match v0 with VCons a0 d0 -> gVal_fo w a0 a fa; gVal_fo w d0 d fd)
  | _ -> ()

(* --- the index family --- *)
(* Rocq states VRel_unfold as an equality of relations and rewrites with it; here it is pointwise. *)
let vRel_unfold (sealed : list name) (dd : list (name & fundef)) (k : nat) (w : world) (v0 v : value)
  : Lemma (vRel sealed dd k w v0 v <==> vBody sealed dd (if k = 0 then bottom_rel else vRelF sealed dd (k - 1)) k w v0 v) =
  ()

(* Rocq: VRelF k j = VRel j (an equality of relations, proved by unfolding). SMT does not prove
   equalities between function values here, so this port states it pointwise and never rewrites
   with relation equalities (see the README). *)
let rec vRelF_index (sealed : list name) (dd : list (name & fundef)) (k j : nat) (w : world) (v0 v : value)
  : Lemma (requires j <= k) (ensures vRelF sealed dd k j w v0 v <==> vRel sealed dd j w v0 v) (decreases k) =
  if k = 0 then ()
  else if j <= k - 1 then vRelF_index sealed dd (k - 1) j w v0 v
  else ()

let rec vBody_ground (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w : world) (v0 v : value)
  : Lemma (requires vBody sealed dd vv k w v0 v) (ensures gVal w v0 v) (decreases v0) =
  match v0, v with
  | VCons a0 d0, VCons a d -> vBody_ground sealed dd vv k w a0 a; vBody_ground sealed dd vv k w d0 d
  | VPartial _ l0, VPartial _ l -> vBody_list_ground sealed dd vv k w l0 l
  | _ -> ()
and vBody_list_ground (sealed : list name) (dd : list (name & fundef)) (vv : vrelt) (k : nat) (w : world) (l0 l : list value)
  : Lemma (requires vBody_list sealed dd vv k w l0 l) (ensures gVal_list w l0 l) (decreases l0) =
  match l0, l with
  | x0 :: r0, x :: r -> vBody_ground sealed dd vv k w x0 x; vBody_list_ground sealed dd vv k w r0 r
  | _ -> ()

let vRel_ground (sealed : list name) (dd : list (name & fundef)) (k : nat) (w : world) (v0 v : value)
  : Lemma (requires vRel sealed dd k w v0 v) (ensures gVal w v0 v) =
  vRel_unfold sealed dd k w v0 v;
  vBody_ground sealed dd (if k = 0 then bottom_rel else vRelF sealed dd (k - 1)) k w v0 v

let rec forall2_glob_impl (v1 : world -> value -> value -> prop) (w : world) (a b : list (name & value))
  : Lemma (requires (forall x y. v1 w x y ==> gVal w x y) /\ forall2_l (glob_rel v1 w) a b)
          (ensures forall2_l (glob_rel gVal w) a b) =
  match a, b with _ :: a', _ :: b' -> forall2_glob_impl v1 w a' b' | _ -> ()
let rec forall2_cells_impl (v1 : world -> value -> value -> prop) (w : world) (a b : list value)
  : Lemma (requires (forall x y. v1 w x y ==> gVal w x y) /\ forall2_l (v1 w) a b)
          (ensures forall2_l (gVal w) a b) =
  match a, b with _ :: a', _ :: b' -> forall2_cells_impl v1 w a' b' | _ -> ()

let sRel_with_ground (dd : list (name & fundef)) (v1 : world -> value -> value -> prop) (w : world) (s0 s : store)
  : Lemma (requires (forall x y. v1 w x y ==> gVal w x y) /\ sRel_with dd v1 w s0 s) (ensures gStore w s0 s) =
  forall2_glob_impl v1 w s0.gvals s.gvals;
  introduce forall (l0 l : nat). mem_l (l0, l) w ==> (exists c0 c. nth_error s0.heap l0 == Some c0 /\
     nth_error s.heap l == Some c /\ forall2_l (gVal w) c0 c)
  with introduce _ ==> _ with
    eliminate exists c0 c. nth_error s0.heap l0 == Some c0 /\ nth_error s.heap l == Some c /\ forall2_l (v1 w) c0 c
    with forall2_cells_impl v1 w c0 c

let sRel_ground (sealed : list name) (dd : list (name & fundef)) (k : nat) (w : world) (s0 s : store)
  : Lemma (requires sRel sealed dd k w s0 s) (ensures gStore w s0 s) =
  introduce forall x y. vRel sealed dd k w x y ==> gVal w x y
  with introduce _ ==> _ with vRel_ground sealed dd k w x y;
  sRel_with_ground dd (vRel sealed dd k) w s0 s

(* --- the empty continuation --- *)
let inhabits (#t : Type0) (x : t) : Lemma (inhabited t) = ()

let obs_top_throw (sealed : list name) (j : nat) (w : world) (x : exn) (s0 s : store)
  : Lemma (requires wf_world w /\ gStore w s0 s) (ensures obsT sealed j w (cfg (Throw x) [] s0) (cfg (Throw x) [] s)) =
  introduce forall (n : nat) (t : trace) (c' : config). n < j ==> (forall (h : runs sealed n (cfg (Throw x) [] s) t c').
   (forall v s'. c' == cfg (Ret v) [] s' ==> (exists v0 s0' w'.
      srun sealed (cfg (Throw x) [] s0) t (cfg (Ret v0) [] s0') /\ wext w w' /\ gVal w' v0 v /\ gStore w' s0' s')) /\
   (forall x' s'. c' == cfg (Throw x') [] s' ==> (exists s0' w'.
      srun sealed (cfg (Throw x) [] s0) t (cfg (Throw x') [] s0') /\ wext w w' /\ gStore w' s0' s')) /\
   (forall why. next_r (rr sealed) pr c' == MWrong why ==> (exists c0' why0.
      srun sealed (cfg (Throw x) [] s0) t c0' /\ next_r (rr sealed) pr c0' == MWrong why0)))
  with introduce _ ==> _ with
  introduce forall (h : runs sealed n (cfg (Throw x) [] s) t c'). _
  with (match h with
    | Runs_0 _ -> inhabits (Star_refl #config #(step_r (rr sealed) pr) (cfg (Throw x) [] s0))
    | Runs_S _ _ l c1 _ _ st _ -> no_step_from_throw_top sealed x s l c1 st)

let obs_top_ret (sealed : list name) (j : nat) (w : world) (v0 v : value) (s0 s : store)
  : Lemma (requires wf_world w /\ gVal w v0 v /\ gStore w s0 s)
          (ensures obsT sealed j w (cfg (Ret v0) [] s0) (cfg (Ret v) [] s)) =
  introduce forall (n : nat) (t : trace) (c' : config). n < j ==> (forall (h : runs sealed n (cfg (Ret v) [] s) t c').
   (forall v' s'. c' == cfg (Ret v') [] s' ==> (exists v0' s0' w'.
      srun sealed (cfg (Ret v0) [] s0) t (cfg (Ret v0') [] s0') /\ wext w w' /\ gVal w' v0' v' /\ gStore w' s0' s')) /\
   (forall x' s'. c' == cfg (Throw x') [] s' ==> (exists s0' w'.
      srun sealed (cfg (Ret v0) [] s0) t (cfg (Throw x') [] s0') /\ wext w w' /\ gStore w' s0' s')) /\
   (forall why. next_r (rr sealed) pr c' == MWrong why ==> (exists c0' why0.
      srun sealed (cfg (Ret v0) [] s0) t c0' /\ next_r (rr sealed) pr c0' == MWrong why0)))
  with introduce _ ==> _ with
  introduce forall (h : runs sealed n (cfg (Ret v) [] s) t c'). _
  with (match h with
    | Runs_0 _ -> inhabits (Star_refl #config #(step_r (rr sealed) pr) (cfg (Ret v0) [] s0))
    | Runs_S _ _ l c1 t1 _ st rest ->
      step_from_ret_top sealed v s l c1 st;
      (match st with
       | Step_r_resource _ r xx _ _ ->
         (match rest with
          | Runs_0 _ ->
            let st0 : step_r (rr sealed) pr (cfg (Ret v0) [] s0) Tau (cfg (Throw xx) [] s0) =
              Step_r_resource (cfg (Ret v0) [] s0) r xx () () in
            inhabits (Star_step (cfg (Ret v0) [] s0) Tau (cfg (Throw xx) [] s0) [] (cfg (Throw xx) [] s0) st0 (Star_refl _))
          | Runs_S _ _ l2 c2 _ _ st2 _ -> no_step_from_throw_top sealed xx s l2 c2 st2)))

let kRel_top (sealed : list name) (dd : list (name & fundef)) (k : nat) (w : world)
  : Lemma (requires wf_world w) (ensures kRel sealed dd k w [] []) =
  introduce forall (j : nat). j <= k ==> (forall w'. wext w w' ==>
   ((forall v0 v s0 s. vRelF sealed dd k j w' v0 v ==> sRel_with dd (vRelF sealed dd k j) w' s0 s ==>
       obsT sealed j w' (cfg (Ret v0) [] s0) (cfg (Ret v) [] s)) /\
    (forall x s0 s. sRel_with dd (vRelF sealed dd k j) w' s0 s ==>
       obsT sealed j w' (cfg (Throw x) [] s0) (cfg (Throw x) [] s))))
  with introduce _ ==> _ with begin
    introduce forall w' x y. vRelF sealed dd k j w' x y ==> gVal w' x y
    with introduce _ ==> _ with (vRelF_index sealed dd k j w' x y; vRel_ground sealed dd j w' x y);
    introduce forall w'. wext w w' ==> _ with introduce _ ==> _ with begin
      introduce forall v0 v s0 s. vRelF sealed dd k j w' v0 v ==> sRel_with dd (vRelF sealed dd k j) w' s0 s ==>
         obsT sealed j w' (cfg (Ret v0) [] s0) (cfg (Ret v) [] s)
      with introduce _ ==> _ with introduce _ ==> _ with begin
        sRel_with_ground dd (vRelF sealed dd k j) w' s0 s;
        obs_top_ret sealed j w' v0 v s0 s
      end;
      introduce forall x s0 s. sRel_with dd (vRelF sealed dd k j) w' s0 s ==>
         obsT sealed j w' (cfg (Throw x) [] s0) (cfg (Throw x) [] s)
      with introduce _ ==> _ with begin
        sRel_with_ground dd (vRelF sealed dd k j) w' s0 s;
        obs_top_throw sealed j w' x s0 s
      end
    end
  end
