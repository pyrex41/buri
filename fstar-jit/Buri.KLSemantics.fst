(* Port of rocq/KLSemantics.v: eval-kl's reader (parse), the primitive rule table, and the
   small-step machine `next` with its labeled step relation.
   Encoding notes: parse's local fixpoints `args` and `clauses` are mutual functions
   (parse_args, parse_clauses); `step` is a Type-valued inductive family (Rocq: Prop). *)
module Buri.KLSemantics
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue

(* ---------- eval-kl: data to resolved syntax ---------- *)
let kw (s : string) : name = of_string s
let keyword (s : name) : bool =
  existsb (text_eqb s) (map kw ["lambda"; "let"; "if"; "and"; "or"; "cond"; "trap-error"; "defun"; "freeze"; "type"])
let bound (scope : list name) (s : name) : bool = existsb (text_eqb s) scope
let rec symbols (v : value) : option (list name) =
  match v with
  | VNil -> Some []
  | VCons (VSym x) d -> option_map (Cons x) (symbols d)
  | _ -> None

let rec parse (scope : list name) (v : value) : Tot (option expr) (decreases v) =
  match v with
  | VNum n -> Some (ENum n) | VStr t -> Some (EStr t) | VBool b -> Some (EBool b) | VNil -> Some ENil
  | VSym s -> Some (if bound scope s then EVar s else ESym s)
  | VCons h t ->
    (match h with
     | VSym s ->
       if text_eqb s (kw "lambda") then (match t with
         | VCons (VSym x) (VCons b VNil) -> option_map (ELam x) (parse (x :: scope) b) | _ -> None)
       else if text_eqb s (kw "let") then (match t with
         | VCons (VSym x) (VCons a (VCons b VNil)) -> (match parse scope a, parse (x :: scope) b with
           | Some ea, Some eb -> Some (ELet x ea eb) | _, _ -> None)
         | _ -> None)
       else if text_eqb s (kw "if") then (match t with
         | VCons c (VCons a (VCons b VNil)) -> (match parse scope c, parse scope a, parse scope b with
           | Some ec, Some ea, Some eb -> Some (EIf ec ea eb) | _, _, _ -> None)
         | _ -> None)
       else if text_eqb s (kw "and") then (match t with
         | VCons a (VCons b VNil) -> (match parse scope a, parse scope b with
           | Some ea, Some eb -> Some (EAnd ea eb) | _, _ -> None)
         | _ -> None)
       else if text_eqb s (kw "or") then (match t with
         | VCons a (VCons b VNil) -> (match parse scope a, parse scope b with
           | Some ea, Some eb -> Some (EOr ea eb) | _, _ -> None)
         | _ -> None)
       else if text_eqb s (kw "cond") then option_map ECond (parse_clauses scope t)
       else if text_eqb s (kw "trap-error") then (match t with
         | VCons a (VCons b VNil) -> (match parse scope a, parse scope b with
           | Some ea, Some eb -> Some (ETrap ea eb) | _, _ -> None)
         | _ -> None)
       else if text_eqb s (kw "defun") then (match t with
         | VCons (VSym f) (VCons ps (VCons b VNil)) -> (match symbols ps with
           | Some xs -> option_map (EDefun f xs) (parse xs b) | None -> None)
         | _ -> None)
       else if text_eqb s (kw "freeze") then (match t with
         | VCons a VNil -> option_map EFreeze (parse scope a) | _ -> None)
       else if text_eqb s (kw "type") then (match t with
         | VCons a (VCons _ VNil) -> option_map EType (parse scope a) | _ -> None)
       else if bound scope s then option_map (EApp (EVar s)) (parse_args scope t)
       else option_map (ECall s) (parse_args scope t)
     | _ -> (match parse scope h, parse_args scope t with Some eh, Some es -> Some (EApp eh es) | _, _ -> None))
  | _ -> None
and parse_args (scope : list name) (v : value) : Tot (option (list expr)) (decreases v) =
  match v with
  | VNil -> Some []
  | VCons a d -> (match parse scope a, parse_args scope d with Some e, Some es -> Some (e :: es) | _, _ -> None)
  | _ -> None
and parse_clauses (scope : list name) (v : value) : Tot (option (list (expr & expr))) (decreases v) =
  match v with
  | VNil -> Some []
  | VCons (VCons c (VCons b VNil)) more -> (match parse scope c, parse scope b, parse_clauses scope more with
    | Some ec, Some eb, Some cs -> Some ((ec, eb) :: cs) | _, _, _ -> None)
  | _ -> None

(* ---------- primitive rules ---------- *)
type pout =
  | ORet : v:value -> s:store -> pout
  | OThrow : x:exn -> pout
  | OEval : e:expr -> pout
  | OFail : r:resource -> pout
  | OWrong : why:text -> pout
noeq type presult = | PDone : o:pout -> presult | PIO : q:request -> k:(response -> pout) -> presult

let ret v s = PDone (ORet v s)
let throw x = PDone (OThrow x)
let dom p = PDone (OThrow (XPrim p))

let rule_intern (args : list value) (s : store) : presult = match args with
  | [VStr t] -> ret (if text_eqb t (kw "true") then VBool true
                     else if text_eqb t (kw "false") then VBool false else VSym t) s
  | _ -> dom PIntern
let rule_pos (args : list value) (s : store) : presult = match args with
  | [VStr t; VNum (NInt z)] -> if 0 <= z && z < length t
      then (match nth_error t (to_nat z) with Some c -> ret (VStr [c]) s | None -> throw XBounds)
      else throw XBounds
  | _ -> dom PPos
let rule_tlstr (args : list value) (s : store) : presult = match args with
  | [VStr (_ :: t)] -> ret (VStr t) s | [VStr []] -> throw XBounds | _ -> dom PTlstr
let rule_cn (args : list value) (s : store) : presult = match args with
  | [VStr a; VStr b] -> ret (VStr (app a b)) s | _ -> dom PCn
let rule_str (pr : profile) (args : list value) (s : store) : presult = match args with
  | [VNum (NInt z)] -> ret (VStr (dec_text z)) s
  | [VNum (NFloat f)] -> ret (VStr (pr.float_text f)) s
  | [VSym x] -> ret (VStr x) s
  | [VBool b] -> ret (VStr (bool_text b)) s
  | [v] -> (match pr.str_other v with Some t -> ret (VStr t) s | None -> dom PStr)
  | _ -> dom PStr
let rule_stringp (args : list value) (s : store) : presult = match args with
  | [VStr _] -> ret (VBool true) s | [_] -> ret (VBool false) s | _ -> dom PStringP
let rule_n_to_string (args : list value) (s : store) : presult = match args with
  | [VNum (NInt z)] -> if scalar_ok z then ret (VStr [to_nat z]) s else dom PNToString
  | _ -> dom PNToString
let rule_string_to_n (args : list value) (s : store) : presult = match args with
  | [VStr (c :: _)] -> ret (VNum (NInt c)) s | [VStr []] -> throw XBounds
  | _ -> dom PStringToN
let rule_set (args : list value) (s : store) : presult = match args with
  | [VSym x; v] -> ret v (mkStore s.heap ((x, v) :: s.gvals) s.gfuns)
  | _ -> dom PSet
let rule_value (args : list value) (s : store) : presult = match args with
  | [VSym x] -> (match lookup x s.gvals with Some v -> ret v s | None -> throw (XUnboundGlobal x))
  | _ -> dom PValue
let rule_simple_error (args : list value) (s : store) : presult = match args with
  | [VStr t] -> throw (XUser t) | _ -> dom PSimpleError
let rule_error_to_string (pr : profile) (args : list value) (s : store) : presult = match args with
  | [VExn (XUser t)] -> ret (VStr t) s
  | [VExn x] -> ret (VStr (pr.sys_message x)) s
  | _ -> dom PErrorToString
let rule_cons (args : list value) (s : store) : presult = match args with [a; b] -> ret (VCons a b) s | _ -> dom PCons
let rule_hd (args : list value) (s : store) : presult = match args with [VCons a _] -> ret a s | _ -> dom PHd
let rule_tl (args : list value) (s : store) : presult = match args with [VCons _ d] -> ret d s | _ -> dom PTl
let rule_consp (args : list value) (s : store) : presult = match args with
  | [VCons _ _] -> ret (VBool true) s | [_] -> ret (VBool false) s | _ -> dom PConsP
let rule_equal (pr : profile) (args : list value) (s : store) : presult = match args with
  | [a; b] -> (match kl_eq pr s.heap a b with
    | Some r -> ret (VBool r) s | None -> PDone (OWrong (kw "equality-undefined")))
  | _ -> dom PEqual
let rule_eval_kl (args : list value) (s : store) : presult = match args with
  | [d] -> (match parse [] d with Some e -> PDone (OEval e) | None -> throw XEvalKL)
  | _ -> dom PEvalKL
let rule_absvector (pr : profile) (args : list value) (s : store) : presult = match args with
  | [VNum (NInt z)] -> if 0 <= z then
      (if alloc_ok pr s.heap (to_nat z)
       then ret (VVec (length s.heap))
                (mkStore (app s.heap [repeat pr.absvector_fill (to_nat z)]) s.gvals s.gfuns)
       else PDone (OFail RHeap))
    else dom PAbsvector
  | _ -> dom PAbsvector
let rule_address_set (args : list value) (s : store) : presult = match args with
  | [VVec l; VNum (NInt z); x] -> (match nth_error s.heap l with
    | Some cells -> if 0 <= z && z < length cells
      then ret (VVec l) (mkStore (replace_nth l (replace_nth (to_nat z) x cells) s.heap) s.gvals s.gfuns)
      else throw XBounds
    | None -> PDone (OWrong (kw "dangling-location")))
  | _ -> dom PAddressSet
let rule_address_get (args : list value) (s : store) : presult = match args with
  | [VVec l; VNum (NInt z)] -> (match nth_error s.heap l with
    | Some cells -> if 0 <= z then (match nth_error cells (to_nat z) with
        | Some v -> ret v s | None -> throw XBounds) else throw XBounds
    | None -> PDone (OWrong (kw "dangling-location")))
  | _ -> dom PAddressGet
let rule_absvectorp (args : list value) (s : store) : presult = match args with
  | [VVec _] -> ret (VBool true) s | [_] -> ret (VBool false) s | _ -> dom PAbsvectorP

let io_fail (r : response) : pout = match r with
  | RFailed e -> OThrow (XIO e) | _ -> OThrow (XIO EProtocol)
let rule_write_byte (args : list value) (s : store) : presult = match args with
  | [VNum (NInt b); VStream h] -> if 0 <= b && b < 256
    then PIO (QWrite h [to_nat b]) (fun r -> match r with
      | RWrote c -> if c = 1 then ORet (VNum (NInt b)) s
                    else if c = 0 then OThrow (XIO EShortWrite) else OThrow (XIO EProtocol)
      | r -> io_fail r)
    else dom PWriteByte
  | _ -> dom PWriteByte
let rule_read_byte (args : list value) (s : store) : presult = match args with
  | [VStream h] -> PIO (QRead h 1) (fun r -> match r with
    | RRead [b] -> if b < 256 then ORet (VNum (NInt b)) s else OThrow (XIO EProtocol)
    | RRead [] | REof -> ORet (VNum (NInt (-1))) s
    | r -> io_fail r)
  | _ -> dom PReadByte
let rule_open (args : list value) (s : store) : presult = match args with
  | [VStr path; VSym d] ->
    let go dir = PIO (QOpen path dir) (fun r -> match r with
      | ROpened h -> ORet (VStream h) s | r -> io_fail r) in
    if text_eqb d (kw "in") then go DIn else if text_eqb d (kw "out") then go DOut else dom POpen
  | _ -> dom POpen
let rule_close (args : list value) (s : store) : presult = match args with
  | [VStream h] -> PIO (QClose h) (fun r -> match r with RClosed -> ORet VNil s | r -> io_fail r)
  | _ -> dom PClose
let rule_get_time (pr : profile) (args : list value) (s : store) : presult = match args with
  | [VSym k] -> PIO (QTime k) (fun r -> match r with
    | RTime z -> (match pr.time_value k z with Some n -> ORet (VNum n) s | None -> OThrow (XPrim PGetTime))
    | r -> io_fail r)
  | _ -> dom PGetTime

let rule_arith (pr : profile) (p : prim) (iop : int -> int -> int) (args : list value) (s : store) : presult =
  match args with
  | [VNum a; VNum b] -> (match int_or pr p iop a b with Some n -> ret (VNum n) s | None -> dom p)
  | _ -> dom p
let rule_div (pr : profile) (args : list value) (s : store) : presult = match args with
  | [VNum a; VNum b] -> (match num_div pr a b with
    | None -> throw XDivZero | Some (Some n) -> ret (VNum n) s | Some None -> dom PDiv)
  | _ -> dom PDiv
let rule_cmp (pr : profile) (p : prim) (args : list value) (s : store) : presult = match args with
  | [VNum a; VNum b] -> ret (VBool (num_cmp pr p a b)) s | _ -> dom p
let rule_numberp (args : list value) (s : store) : presult = match args with
  | [VNum _] -> ret (VBool true) s | [_] -> ret (VBool false) s | _ -> dom PNumberP

let zadd (x y : int) : int = x + y
let zsub (x y : int) : int = x - y
let zmul (x y : int) : int = x * y

let prim_rule (pr : profile) (p : prim) (args : list value) (s : store) : presult =
  match p with
  | PIntern -> rule_intern args s
  | PPos -> rule_pos args s | PTlstr -> rule_tlstr args s | PCn -> rule_cn args s
  | PStr -> rule_str pr args s | PStringP -> rule_stringp args s
  | PNToString -> rule_n_to_string args s | PStringToN -> rule_string_to_n args s
  | PSet -> rule_set args s | PValue -> rule_value args s
  | PSimpleError -> rule_simple_error args s | PErrorToString -> rule_error_to_string pr args s
  | PCons -> rule_cons args s | PHd -> rule_hd args s | PTl -> rule_tl args s | PConsP -> rule_consp args s
  | PEqual -> rule_equal pr args s | PEvalKL -> rule_eval_kl args s
  | PAbsvector -> rule_absvector pr args s | PAddressSet -> rule_address_set args s
  | PAddressGet -> rule_address_get args s | PAbsvectorP -> rule_absvectorp args s
  | PWriteByte -> rule_write_byte args s | PReadByte -> rule_read_byte args s
  | POpen -> rule_open args s | PClose -> rule_close args s
  | PGetTime -> rule_get_time pr args s
  | PAdd -> rule_arith pr PAdd zadd args s | PSub -> rule_arith pr PSub zsub args s
  | PMul -> rule_arith pr PMul zmul args s | PDiv -> rule_div pr args s
  | PGt -> rule_cmp pr PGt args s | PLt -> rule_cmp pr PLt args s
  | PGe -> rule_cmp pr PGe args s | PLe -> rule_cmp pr PLe args s
  | PNumberP -> rule_numberp args s

(* ---------- machine ---------- *)
type frame =
  | KLet : x:name -> body:expr -> rho:lenv -> frame
  | KIf : a:expr -> b:expr -> rho:lenv -> frame
  | KAnd : b:expr -> rho:lenv -> frame | KAndR
  | KOr : b:expr -> rho:lenv -> frame | KOrR
  | KCond : body:expr -> rest:list (expr & expr) -> rho:lenv -> frame
  | KTrap : handler:expr -> rho:lenv -> frame
  | KHead : args:list expr -> rho:lenv -> frame
  | KArgs : f:value -> fdone:list value -> rest:list expr -> rho:lenv -> frame
  | KCallArgs : f:name -> fdone:list value -> rest:list expr -> rho:lenv -> frame
  | KApply : args:list value -> frame

type control =
  | Eval : rho:lenv -> e:expr -> control
  | Ret : v:value -> control
  | Throw : x:exn -> control
  | Fail : r:resource -> control
  | Halted : ev:env_event -> control
  | Wrong : why:text -> control

type config = { ctl : control; kont : list frame; mem : store }
let cfg c k s : config = { ctl = c; kont = k; mem = s }
type kl_outcome = outcome value exn

noeq type move =
  | MTau : c:config -> move
  | MIO : q:request -> k:(response -> config) -> move
  | MFinal : o:kl_outcome -> move
  | MWrong : why:text -> move

let push (pr : profile) (f : frame) (k : list frame) (c : control) (s : store) : config =
  match pr.stack_limit with
  | Some n -> if n <= length k then cfg (Fail RStack) k s else cfg c (f :: k) s
  | None -> cfg c (f :: k) s
let continue_with (pr : profile) (rest : list value) (k : list frame) (c : control) (s : store) : config =
  match rest with [] -> cfg c k s | _ -> push pr (KApply rest) k c s

let pout_config (pr : profile) (o : pout) (rest : list value) (k : list frame) (s : store) : config =
  match o with
  | ORet v s' -> continue_with pr rest k (Ret v) s'
  | OThrow x -> cfg (Throw x) k s
  | OEval e -> continue_with pr rest k (Eval [] e) s
  | OFail r -> cfg (Fail r) k s
  | OWrong w -> cfg (Wrong w) k s

let prim_move pr p args rest k s : move =
  match prim_rule pr p args s with
  | PDone o -> MTau (pout_config pr o rest k s)
  | PIO q kont -> MIO q (fun r -> pout_config pr (kont r) rest k s)

let call_named (pr : profile) (g : name) (args : list value) (k : list frame) (s : store) : move =
  match lookup g s.gfuns with
  | None -> MTau (cfg (Throw (XUndefinedFun g)) k s)
  | Some (FUser ps body) ->
    if length args < length ps then MTau (cfg (Ret (VPartial g args)) k s)
    else MTau (continue_with pr (skipn (length ps) args) k
                 (Eval (combine ps (firstn (length ps) args)) body) s)
  | Some (FPrim p) ->
    if length args < prim_arity p then MTau (cfg (Ret (VPartial g args)) k s)
    else prim_move pr p (firstn (prim_arity p) args) (skipn (prim_arity p) args) k s

let apply_value (pr : profile) (f : value) (args : list value) (k : list frame) (s : store) : move =
  match f, args with
  | VFrozen body rho, [] -> MTau (cfg (Eval rho body) k s)
  | VLam x body rho, a :: rest -> MTau (continue_with pr rest k (Eval ((x, a) :: rho) body) s)
  | VPartial g prev, _ -> call_named pr g (app prev args) k s
  | VFrozen _ _, _ :: _ | VLam _ _ _, [] -> MTau (cfg (Throw XArity) k s)
  | _, _ -> MTau (cfg (Throw XNotCallable) k s)

let rec nodupb (l : list name) : bool =
  match l with [] -> true | x :: l -> not (bound l x) && nodupb l

let eval_move (pr : profile) (rho : lenv) (e : expr) (k : list frame) (s : store) : move =
  match e with
  | ENum n -> MTau (cfg (Ret (VNum n)) k s)
  | EStr t -> MTau (cfg (Ret (VStr t)) k s)
  | ESym x -> MTau (cfg (Ret (VSym x)) k s)
  | EBool b -> MTau (cfg (Ret (VBool b)) k s)
  | ENil -> MTau (cfg (Ret VNil) k s)
  | EVar x -> MTau (cfg (match lookup x rho with Some v -> Ret v | None -> Throw (XUnboundVar x)) k s)
  | ELam x b -> MTau (cfg (Ret (VLam x b rho)) k s)
  | EFreeze b -> MTau (cfg (Ret (VFrozen b rho)) k s)
  | ELet x a b -> MTau (push pr (KLet x b rho) k (Eval rho a) s)
  | EIf c a b -> MTau (push pr (KIf a b rho) k (Eval rho c) s)
  | EAnd a b -> MTau (push pr (KAnd b rho) k (Eval rho a) s)
  | EOr a b -> MTau (push pr (KOr b rho) k (Eval rho a) s)
  | ECond [] -> MTau (cfg (Throw XCondFail) k s)
  | ECond ((c, b) :: rest) -> MTau (push pr (KCond b rest rho) k (Eval rho c) s)
  | ETrap a h -> MTau (push pr (KTrap h rho) k (Eval rho a) s)
  | EType a -> MTau (cfg (Eval rho a) k s)
  | EDefun f ps b -> if nodupb ps then
      MTau (cfg (Ret (VSym f)) k (mkStore s.heap s.gvals ((f, FUser ps b) :: s.gfuns)))
    else MTau (cfg (Throw XBadDefinition) k s)
  | EApp h args -> MTau (push pr (KHead args rho) k (Eval rho h) s)
  | ECall f [] -> call_named pr f [] k s
  | ECall f (a :: rest) -> MTau (push pr (KCallArgs f [] rest rho) k (Eval rho a) s)

let ret_move (pr : profile) (v : value) (f : frame) (k : list frame) (s : store) : move =
  match f with
  | KLet x b rho -> MTau (cfg (Eval ((x, v) :: rho) b) k s)
  | KIf a b rho -> MTau (cfg (match v with
      | VBool true -> Eval rho a | VBool false -> Eval rho b | _ -> Throw XNotBoolean) k s)
  | KAnd b rho -> (match v with
      | VBool true -> MTau (push pr KAndR k (Eval rho b) s)
      | VBool false -> MTau (cfg (Ret (VBool false)) k s)
      | _ -> MTau (cfg (Throw XNotBoolean) k s))
  | KOr b rho -> (match v with
      | VBool true -> MTau (cfg (Ret (VBool true)) k s)
      | VBool false -> MTau (push pr KOrR k (Eval rho b) s)
      | _ -> MTau (cfg (Throw XNotBoolean) k s))
  | KAndR | KOrR -> MTau (cfg (match v with VBool b -> Ret (VBool b) | _ -> Throw XNotBoolean) k s)
  | KCond b rest rho -> MTau (cfg (match v with
      | VBool true -> Eval rho b | VBool false -> Eval rho (ECond rest) | _ -> Throw XNotBoolean) k s)
  | KTrap _ _ -> MTau (cfg (Ret v) k s)
  | KHead [] rho -> apply_value pr v [] k s
  | KHead (a :: rest) rho -> MTau (cfg (Eval rho a) (KArgs v [] rest rho :: k) s)
  | KArgs fv done [] rho -> apply_value pr fv (rev (v :: done)) k s
  | KArgs fv done (a :: rest) rho -> MTau (cfg (Eval rho a) (KArgs fv (v :: done) rest rho :: k) s)
  | KCallArgs g done [] rho -> call_named pr g (rev (v :: done)) k s
  | KCallArgs g done (a :: rest) rho -> MTau (cfg (Eval rho a) (KCallArgs g (v :: done) rest rho :: k) s)
  | KApply args -> apply_value pr v args k s

let throw_move (x : exn) (f : frame) (k : list frame) (s : store) : move =
  match f with
  | KTrap h rho -> MTau (cfg (Eval rho h) (KApply [VExn x] :: k) s)
  | _ -> MTau (cfg (Throw x) k s)

let next (pr : profile) (c : config) : move =
  match c.ctl with
  | Eval rho e -> eval_move pr rho e c.kont c.mem
  | Ret v -> (match c.kont with [] -> MFinal (Normal v) | f :: k -> ret_move pr v f k c.mem)
  | Throw x -> (match c.kont with [] -> MFinal (Error x) | f :: k -> throw_move x f k c.mem)
  | Fail r -> MFinal (ResourceOut r)
  | Halted (Signal sg) -> MFinal (Killed sg)
  | Halted Cancel -> MFinal Cancelled
  | Wrong w -> MWrong w

noeq type step (pr : profile) : config -> label -> config -> Type =
  | Step_tau : c:config -> c':config -> squash (next pr c == MTau c') -> step pr c Tau c'
  | Step_io : c:config -> q:request -> kk:(response -> config) -> r:response ->
      squash (next pr c == MIO q kk) -> step pr c (Obs (EvIO q r)) (kk r)
let final (pr : profile) (c : config) (o : kl_outcome) : prop = next pr c == MFinal o
let wrong (pr : profile) (c : config) : prop = exists w. next pr c == MWrong w
