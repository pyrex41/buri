(* Port of rocq/KLPort.v: per-port options on the KLambda semantics, `next_r`, `step_r`, and the
   theorem that the agreed options give exactly KLSemantics.next. *)
module Buri.KLPort
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics

noeq type port_rules = {
  int_range : option (int & int);
  char_ok : int -> bool;
  object_identity : bool;
  arity_errors : bool;
  defun_allowed : store -> name -> bool;
  time_kind_ok : text -> bool;
  unchecked_writes : bool;
  resource_exn : resource -> option exn }

let agreed_rules : port_rules = {
  int_range = None; char_ok = scalar_ok; object_identity = false; arity_errors = false;
  defun_allowed = (fun _ _ -> true); time_kind_ok = (fun _ -> true); unchecked_writes = false;
  resource_exn = (fun _ -> None) }

(* ---------- 1: integer range ---------- *)
let in_range (rr : port_rules) (z : int) : bool = match rr.int_range with
  | None -> true
  | Some (lo, hi) -> lo <= z && z <= hi

let rule_arith_r rr pr p (iop : int -> int -> int) args s : presult = match args with
  | [VNum (NInt x); VNum (NInt y)] ->
    if in_range rr (iop x y) then rule_arith pr p iop args s else dom p
  | _ -> rule_arith pr p iop args s

let rule_div_r rr pr args s : presult = match args with
  | [VNum (NInt x); VNum (NInt y)] ->
    if not (y = 0) && zrem x y = 0 && not (in_range rr (zquot x y))
    then dom PDiv else rule_div pr args s
  | _ -> rule_div pr args s

(* ---------- 2: characters ---------- *)
let rule_n_to_string_r rr args s : presult = match args with
  | [VNum (NInt z)] -> if rr.char_ok z then ret (VStr [to_nat z]) s else dom PNToString
  | _ -> dom PNToString

(* ---------- 3: identity ---------- *)
let id_key : name = [0; 105; 100]
let closure_id (rho : lenv) : option nat = match rho with
  | (k, VVec l) :: _ -> if text_eqb k id_key then Some l else None
  | _ -> None

let opaque_eq (a b : value) : option bool = match a, b with
  | VLam _ _ r1, VLam _ _ r2 | VFrozen _ r1, VFrozen _ r2 ->
    (match closure_id r1, closure_id r2 with
     | Some x, Some y -> Some (x = y)
     | _, _ -> None)
  | VLam _ _ _, VFrozen _ _ | VFrozen _ _, VLam _ _ _ -> Some false
  | _, _ -> None

let eq_opaque_r (rr : port_rules) (a b : value) : option bool =
  if rr.object_identity then opaque_eq a b else None

let rec eq_depth_r (rr : port_rules) (pr : profile) (h : list (list value)) (d : nat) (a b : value)
  : Tot (option bool) (decreases %[d; a]) =
  if d = 0 then None else
  match a, b with
  | VNum x, VNum y -> Some (num_cmp pr PEqual x y)
  | VSym x, VSym y | VStr x, VStr y -> Some (text_eqb x y)
  | VBool x, VBool y -> Some (x = y)
  | VNil, VNil -> Some true
  | VCons a1 a2, VCons b1 b2 ->
    (match eq_depth_r rr pr h d a1 b1 with Some true -> eq_depth_r rr pr h d a2 b2 | r -> r)
  | VStream x, VStream y -> Some (x = y)
  | VVec l1, VVec l2 -> if l1 = l2 then Some true else
      (match nth_error h l1, nth_error h l2 with
       | Some xs, Some ys -> eq_depth_r_list rr pr h (d - 1) xs ys
       | _, _ -> None)
  | _, _ ->
    if is_opaque a then (if is_opaque b then eq_opaque_r rr a b else Some false)
    else if is_opaque b then Some false
    else Some false
and eq_depth_r_list (rr : port_rules) (pr : profile) (h : list (list value)) (d : nat) (xs ys : list value)
  : Tot (option bool) (decreases %[d; xs]) =
  match xs, ys with
  | [], [] -> Some true
  | x :: xs', y :: ys' -> (match eq_depth_r rr pr h d x y with Some true -> eq_depth_r_list rr pr h d xs' ys' | r -> r)
  | _, _ -> Some false
let kl_eq_r rr pr h a b = eq_depth_r rr pr h (length h + 1) a b

let rule_equal_r rr pr args s : presult = match args with
  | [a; b] -> (match kl_eq_r rr pr s.heap a b with
    | Some r -> ret (VBool r) s | None -> PDone (OWrong (kw "equality-undefined")))
  | _ -> dom PEqual

let tagged_env (rho : lenv) (s : store) : lenv = (id_key, VVec (length s.heap)) :: rho
let with_cell (s : store) : store = mkStore (app s.heap [[]]) s.gvals s.gfuns

(* ---------- 6 and 7: clock and writes ---------- *)
let rule_get_time_r rr pr args s : presult = match args with
  | [VSym k] -> if rr.time_kind_ok k then rule_get_time pr args s else dom PGetTime
  | _ -> rule_get_time pr args s

let rule_write_byte_r rr args s : presult =
  if rr.unchecked_writes then (match args with
    | [VNum (NInt b); VStream h] -> if 0 <= b && b < 256
      then PIO (QWrite h [to_nat b]) (fun _ -> ORet (VNum (NInt b)) s)
      else dom PWriteByte
    | _ -> dom PWriteByte)
  else rule_write_byte args s

let prim_rule_r (rr : port_rules) (pr : profile) (p : prim) (args : list value) (s : store) : presult =
  match p with
  | PNToString -> rule_n_to_string_r rr args s
  | PEqual -> rule_equal_r rr pr args s
  | PWriteByte -> rule_write_byte_r rr args s
  | PGetTime -> rule_get_time_r rr pr args s
  | PAdd -> rule_arith_r rr pr PAdd zadd args s
  | PSub -> rule_arith_r rr pr PSub zsub args s
  | PMul -> rule_arith_r rr pr PMul zmul args s
  | PDiv -> rule_div_r rr pr args s
  | _ -> prim_rule pr p args s

(* ---------- machine ---------- *)
let prim_move_r rr pr p args rest k s : move =
  match prim_rule_r rr pr p args s with
  | PDone o -> MTau (pout_config pr o rest k s)
  | PIO q kont -> MIO q (fun r -> pout_config pr (kont r) rest k s)

let arity_mismatch (rr : port_rules) (given want : nat) : bool =
  rr.arity_errors && not (given = want)

let call_named_r rr pr (g : name) (args : list value) (k : list frame) (s : store) : move =
  match lookup g s.gfuns with
  | None -> MTau (cfg (Throw (XUndefinedFun g)) k s)
  | Some (FUser ps body) ->
    if arity_mismatch rr (length args) (length ps) then MTau (cfg (Throw XArity) k s)
    else if length args < length ps then MTau (cfg (Ret (VPartial g args)) k s)
    else MTau (continue_with pr (skipn (length ps) args) k
                 (Eval (combine ps (firstn (length ps) args)) body) s)
  | Some (FPrim p) ->
    if arity_mismatch rr (length args) (prim_arity p) then MTau (cfg (Throw XArity) k s)
    else if length args < prim_arity p then MTau (cfg (Ret (VPartial g args)) k s)
    else prim_move_r rr pr p (firstn (prim_arity p) args) (skipn (prim_arity p) args) k s

let apply_value_r rr pr (f : value) (args : list value) (k : list frame) (s : store) : move =
  match f, args with
  | VFrozen body rho, [] -> MTau (cfg (Eval rho body) k s)
  | VLam x body rho, a :: rest -> MTau (continue_with pr rest k (Eval ((x, a) :: rho) body) s)
  | VPartial g prev, _ -> call_named_r rr pr g (app prev args) k s
  | VFrozen _ _, _ :: _ | VLam _ _ _, [] -> MTau (cfg (Throw XArity) k s)
  | _, _ -> MTau (cfg (Throw XNotCallable) k s)

let eval_move_r rr pr (rho : lenv) (e : expr) (k : list frame) (s : store) : move =
  match e with
  | ELam x b -> if rr.object_identity
      then MTau (cfg (Ret (VLam x b (tagged_env rho s))) k (with_cell s))
      else MTau (cfg (Ret (VLam x b rho)) k s)
  | EFreeze b -> if rr.object_identity
      then MTau (cfg (Ret (VFrozen b (tagged_env rho s))) k (with_cell s))
      else MTau (cfg (Ret (VFrozen b rho)) k s)
  | EDefun f ps b ->
    if rr.defun_allowed s f then
      (if nodupb ps then
        MTau (cfg (Ret (VSym f)) k (mkStore s.heap s.gvals ((f, FUser ps b) :: s.gfuns)))
       else MTau (cfg (Throw XBadDefinition) k s))
    else MTau (cfg (Throw XBadDefinition) k s)
  | ECall f [] -> call_named_r rr pr f [] k s
  | _ -> eval_move pr rho e k s

let ret_move_r rr pr (v : value) (f : frame) (k : list frame) (s : store) : move =
  match f with
  | KHead [] rho -> apply_value_r rr pr v [] k s
  | KArgs fv done [] rho -> apply_value_r rr pr fv (rev (v :: done)) k s
  | KCallArgs g done [] rho -> call_named_r rr pr g (rev (v :: done)) k s
  | KApply args -> apply_value_r rr pr v args k s
  | _ -> ret_move pr v f k s

let next_r (rr : port_rules) (pr : profile) (c : config) : move =
  match c.ctl with
  | Eval rho e -> eval_move_r rr pr rho e c.kont c.mem
  | Ret v -> (match c.kont with [] -> MFinal (Normal v) | f :: k -> ret_move_r rr pr v f k c.mem)
  | Throw x -> (match c.kont with [] -> MFinal (Error x) | f :: k -> throw_move x f k c.mem)
  | Fail r -> (match rr.resource_exn r with
    | Some x -> MTau (cfg (Throw x) c.kont c.mem)
    | None -> MFinal (ResourceOut r))
  | Halted (Signal sg) -> MFinal (Killed sg)
  | Halted Cancel -> MFinal Cancelled
  | Wrong w -> MWrong w

let running_state (c : config) : bool = match c.ctl with
  | Eval _ _ | Ret _ -> true | _ -> false

noeq type step_r (rr : port_rules) (pr : profile) : config -> label -> config -> Type0 =
  | Step_r_tau : c:config -> c':config -> squash (next_r rr pr c == MTau c') -> step_r rr pr c Tau c'
  | Step_r_io : c:config -> q:request -> kk:(response -> config) -> r:response ->
      squash (next_r rr pr c == MIO q kk) -> step_r rr pr c (Obs (EvIO q r)) (kk r)
  | Step_r_resource : c:config -> r:resource -> x:exn ->
      squash (running_state c = true) -> squash (rr.resource_exn r == Some x) ->
      step_r rr pr c Tau (cfg (Throw x) c.kont c.mem)

(* ---------- the agreed options are exactly the agreed semantics ---------- *)
let rec eq_depth_r_agreed (pr : profile) (h : list (list value)) (d : nat) (a b : value)
  : Lemma (ensures eq_depth_r agreed_rules pr h d a b == eq_depth pr h d a b) (decreases %[d; a]) =
  if d = 0 then () else
  match a, b with
  | VCons a1 a2, VCons b1 b2 -> eq_depth_r_agreed pr h d a1 b1; eq_depth_r_agreed pr h d a2 b2
  | VVec l1, VVec l2 -> if l1 = l2 then () else
      (match nth_error h l1, nth_error h l2 with
       | Some xs, Some ys -> eq_depth_r_list_agreed pr h (d - 1) xs ys
       | _, _ -> ())
  | _ -> ()
and eq_depth_r_list_agreed (pr : profile) (h : list (list value)) (d : nat) (xs ys : list value)
  : Lemma (ensures eq_depth_r_list agreed_rules pr h d xs ys == eq_depth_list pr h d xs ys) (decreases %[d; xs]) =
  match xs, ys with
  | x :: xs', y :: ys' -> eq_depth_r_agreed pr h d x y; eq_depth_r_list_agreed pr h d xs' ys'
  | _ -> ()

let kl_eq_r_agreed pr h a b : Lemma (kl_eq_r agreed_rules pr h a b == kl_eq pr h a b) =
  eq_depth_r_agreed pr h (length h + 1) a b

let prim_rule_r_agreed (pr : profile) (p : prim) (args : list value) (s : store)
  : Lemma (prim_rule_r agreed_rules pr p args s == prim_rule pr p args s) =
  match p with
  | PEqual -> (match args with [a; b] -> kl_eq_r_agreed pr s.heap a b | _ -> ())
  | _ -> ()

let call_named_r_agreed pr g args k s
  : Lemma (call_named_r agreed_rules pr g args k s == call_named pr g args k s) =
  match lookup g s.gfuns with
  | Some (FPrim p) -> prim_rule_r_agreed pr p (firstn (prim_arity p) args) s
  | _ -> ()

let apply_value_r_agreed pr f args k s
  : Lemma (apply_value_r agreed_rules pr f args k s == apply_value pr f args k s) =
  match f with VPartial g prev -> call_named_r_agreed pr g (app prev args) k s | _ -> ()

let eval_move_r_agreed pr rho e k s
  : Lemma (eval_move_r agreed_rules pr rho e k s == eval_move pr rho e k s) =
  match e with ECall f [] -> call_named_r_agreed pr f [] k s | _ -> ()

let ret_move_r_agreed pr v f k s
  : Lemma (ret_move_r agreed_rules pr v f k s == ret_move pr v f k s) =
  match f with
  | KHead [] rho -> apply_value_r_agreed pr v [] k s
  | KArgs fv done [] rho -> apply_value_r_agreed pr fv (rev (v :: done)) k s
  | KCallArgs g done [] rho -> call_named_r_agreed pr g (rev (v :: done)) k s
  | KApply args -> apply_value_r_agreed pr v args k s
  | _ -> ()

(* The options cannot change the agreed semantics: for every profile and configuration. *)
let next_r_agreed (pr : profile) (c : config) : Lemma (next_r agreed_rules pr c == next pr c) =
  match c.ctl with
  | Eval rho e -> eval_move_r_agreed pr rho e c.kont c.mem
  | Ret v -> (match c.kont with [] -> () | f :: k -> ret_move_r_agreed pr v f k c.mem)
  | _ -> ()

(* step_r agreed and step: each derivation of one gives one of the other. *)
let step_r_agreed_l (pr : profile) (c : config) (l : label) (c' : config) (h : step_r agreed_rules pr c l c')
  : step pr c l c' =
  next_r_agreed pr c;
  match h with
  | Step_r_tau _ _ _ -> Step_tau c c' ()
  | Step_r_io _ q kk r _ -> Step_io c q kk r ()
  | Step_r_resource _ _ _ _ _ -> false_elim ()
let step_r_agreed_r (pr : profile) (c : config) (l : label) (c' : config) (h : step pr c l c')
  : step_r agreed_rules pr c l c' =
  next_r_agreed pr c;
  match h with
  | Step_tau _ _ _ -> Step_r_tau c c' ()
  | Step_io _ q kk r _ -> Step_r_io c q kk r ()

(* ---------- what the options say ---------- *)
let range_raises rr pr p iop x y s
  : Lemma (requires in_range rr (iop x y) = false)
          (ensures rule_arith_r rr pr p iop [VNum (NInt x); VNum (NInt y)] s == dom p) = ()

let no_partial_application rr pr g args k s ps b
  : Lemma (requires rr.arity_errors = true /\ lookup g s.gfuns == Some (FUser ps b) /\ length args <> length ps)
          (ensures call_named_r rr pr g args k s == MTau (cfg (Throw XArity) k s)) = ()

let defun_refused rr pr rho f ps b k s
  : Lemma (requires rr.defun_allowed s f = false)
          (ensures eval_move_r rr pr rho (EDefun f ps b) k s == MTau (cfg (Throw XBadDefinition) k s)) = ()

let unchecked_write_returns rr (b : int) (h : nat) s r
  : Lemma (requires rr.unchecked_writes = true /\ 0 <= b /\ b < 256)
          (ensures exists kk. rule_write_byte_r rr [VNum (NInt b); VStream h] s == PIO (QWrite h [to_nat b]) kk /\
                   kk r == ORet (VNum (NInt b)) s) =
  (* Rocq picks the continuation with eexists; here it is read off the result. *)
  match rule_write_byte_r rr [VNum (NInt b); VStream h] s with
  | PIO q kk -> assert (q == QWrite h [to_nat b] /\ kk r == ORet (VNum (NInt b)) s)
  | PDone _ -> ()

let catchable_resource rr pr r x k s
  : Lemma (requires rr.resource_exn r == Some x)
          (ensures next_r rr pr (cfg (Fail r) k s) == MTau (cfg (Throw x) k s)) = ()

#push-options "--fuel 3"
let closure_identity rr pr h x b r1 r2
  : Lemma (requires rr.object_identity = true)
          (ensures kl_eq_r rr pr h (VLam x b ((id_key, VVec 0) :: r1)) (VLam x b ((id_key, VVec 0) :: r1)) == Some true /\
                   kl_eq_r rr pr h (VLam x b ((id_key, VVec 0) :: r1)) (VLam x b ((id_key, VVec 1) :: r2)) == Some false) =
  text_eqb_refl id_key
#pop-options

let step_r_deterministic_tau (rr : port_rules) (pr : profile) (c c1 c2 : config) (h1 : step_r rr pr c Tau c1) (h2 : step_r rr pr c Tau c2)
  : Lemma (requires forall r. rr.resource_exn r == None) (ensures c1 == c2) =
  match h1 with
  | Step_r_tau _ _ _ -> (match h2 with Step_r_tau _ _ _ -> () | Step_r_resource _ _ _ _ _ -> ())
  | Step_r_resource _ _ _ _ _ -> ()
