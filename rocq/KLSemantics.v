(* E2E-06: small-step KLambda semantics with heap, global namespaces and an
   explicit continuation. One transition function `next` is the rule table;
   `step` is its labeled graph. Every special form and every primitive has a
   named rule (rule_* definitions and the cases of eval_move/ret_move). *)
From Coq Require Import List ZArith NArith String Ascii Bool Lia.
From Buri Require Import Observation KLSyntax KLValue.
Import ListNotations.
Module KLSemantics.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue.

(* ---------- eval-kl: data to resolved syntax ---------- *)
Definition kw (s : string) : name := of_string s.
Definition keyword (s : name) : bool :=
 existsb (text_eqb s) (map kw ["lambda"; "let"; "if"; "and"; "or"; "cond"; "trap-error"; "defun"; "freeze"; "type"]%string).
Definition bound (scope : list name) (s : name) : bool := existsb (text_eqb s) scope.
Fixpoint symbols (v : value) : option (list name) := match v with
 | VNil => Some []
 | VCons (VSym x) d => option_map (cons x) (symbols d)
 | _ => None end.

(* Symbols bound by an enclosing lambda/let/defun parameter are variables,
   other symbols are literals. A keyword head is always a special form; a
   malformed special form, an improper list or a non-data value is rejected. *)
Fixpoint parse (scope : list name) (v : value) {struct v} : option expr :=
 match v with
 | VNum n => Some (ENum n) | VStr t => Some (EStr t) | VBool b => Some (EBool b) | VNil => Some ENil
 | VSym s => Some (if bound scope s then EVar s else ESym s)
 | VCons h t =>
   let args := (fix args (v : value) : option (list expr) := match v with
     | VNil => Some []
     | VCons a d => match parse scope a, args d with Some e, Some es => Some (e :: es) | _, _ => None end
     | _ => None end) in
   match h with
   | VSym s =>
     if text_eqb s (kw "lambda") then match t with
       | VCons (VSym x) (VCons b VNil) => option_map (ELam x) (parse (x :: scope) b) | _ => None end
     else if text_eqb s (kw "let") then match t with
       | VCons (VSym x) (VCons a (VCons b VNil)) => match parse scope a, parse (x :: scope) b with
         | Some ea, Some eb => Some (ELet x ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "if") then match t with
       | VCons c (VCons a (VCons b VNil)) => match parse scope c, parse scope a, parse scope b with
         | Some ec, Some ea, Some eb => Some (EIf ec ea eb) | _, _, _ => None end
       | _ => None end
     else if text_eqb s (kw "and") then match t with
       | VCons a (VCons b VNil) => match parse scope a, parse scope b with
         | Some ea, Some eb => Some (EAnd ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "or") then match t with
       | VCons a (VCons b VNil) => match parse scope a, parse scope b with
         | Some ea, Some eb => Some (EOr ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "cond") then
       option_map ECond ((fix clauses (v : value) : option (list (expr * expr)) := match v with
         | VNil => Some []
         | VCons (VCons c (VCons b VNil)) more => match parse scope c, parse scope b, clauses more with
           | Some ec, Some eb, Some cs => Some ((ec, eb) :: cs) | _, _, _ => None end
         | _ => None end) t)
     else if text_eqb s (kw "trap-error") then match t with
       | VCons a (VCons b VNil) => match parse scope a, parse scope b with
         | Some ea, Some eb => Some (ETrap ea eb) | _, _ => None end
       | _ => None end
     else if text_eqb s (kw "defun") then match t with
       | VCons (VSym f) (VCons ps (VCons b VNil)) => match symbols ps with
         | Some xs => option_map (EDefun f xs) (parse xs b) | None => None end
       | _ => None end
     else if text_eqb s (kw "freeze") then match t with
       | VCons a VNil => option_map EFreeze (parse scope a) | _ => None end
     else if text_eqb s (kw "type") then match t with
       | VCons a (VCons _ VNil) => option_map EType (parse scope a) | _ => None end
     else if bound scope s then option_map (EApp (EVar s)) (args t)
     else option_map (ECall s) (args t)
   | _ => match parse scope h, args t with Some eh, Some es => Some (EApp eh es) | _, _ => None end
   end
 | _ => None end.

(* ---------- primitive rules ---------- *)
Inductive pout :=
 | ORet (v : value) (s : store)
 | OThrow (x : exn)
 | OEval (e : expr)          (* eval-kl: evaluate in the empty lexical environment *)
 | OFail (r : resource)
 | OWrong (why : text).
Inductive presult := PDone (o : pout) | PIO (q : request) (k : response -> pout).

Definition ret v s := PDone (ORet v s).
Definition throw x := PDone (OThrow x).
Definition dom p := PDone (OThrow (XPrim p)).

Definition rule_intern (args : list value) (s : store) := match args with
 | [VStr t] => ret (if text_eqb t (kw "true") then VBool true
                    else if text_eqb t (kw "false") then VBool false else VSym t) s
 | _ => dom PIntern end.
Definition rule_pos args s := match args with
 | [VStr t; VNum (NInt z)] => if (Z.leb 0 z && Z.ltb z (Z.of_nat (List.length t)))%bool
     then match nth_error t (Z.to_nat z) with Some c => ret (VStr [c]) s | None => throw XBounds end
     else throw XBounds
 | _ => dom PPos end.
Definition rule_tlstr args s := match args with
 | [VStr (_ :: t)] => ret (VStr t) s | [VStr []] => throw XBounds | _ => dom PTlstr end.
Definition rule_cn args s := match args with
 | [VStr a; VStr b] => ret (VStr (a ++ b)) s | _ => dom PCn end.
Definition rule_str P args s := match args with
 | [VNum (NInt z)] => ret (VStr (dec_text z)) s
 | [VNum (NFloat f)] => ret (VStr (float_text P f)) s
 | [VSym x] => ret (VStr x) s
 | [VBool b] => ret (VStr (bool_text b)) s
 | [v] => match str_other P v with Some t => ret (VStr t) s | None => dom PStr end
 | _ => dom PStr end.
Definition rule_stringp args s := match args with
 | [VStr _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PStringP end.
Definition rule_n_to_string args s := match args with
 | [VNum (NInt z)] => if scalar_ok z then ret (VStr [Z.to_N z]) s else dom PNToString
 | _ => dom PNToString end.
Definition rule_string_to_n args s := match args with
 | [VStr (c :: _)] => ret (VNum (NInt (Z.of_N c))) s | [VStr []] => throw XBounds
 | _ => dom PStringToN end.
Definition rule_set args s := match args with
 | [VSym x; v] => ret v (Store (heap s) ((x, v) :: gvals s) (gfuns s))
 | _ => dom PSet end.
Definition rule_value args s := match args with
 | [VSym x] => match lookup x (gvals s) with Some v => ret v s | None => throw (XUnboundGlobal x) end
 | _ => dom PValue end.
Definition rule_simple_error args (s : store) := match args with
 | [VStr t] => throw (XUser t) | _ => dom PSimpleError end.
Definition rule_error_to_string P args s := match args with
 | [VExn (XUser t)] => ret (VStr t) s
 | [VExn x] => ret (VStr (sys_message P x)) s
 | _ => dom PErrorToString end.
Definition rule_cons args s := match args with [a; b] => ret (VCons a b) s | _ => dom PCons end.
Definition rule_hd args s := match args with [VCons a _] => ret a s | _ => dom PHd end.
Definition rule_tl args s := match args with [VCons _ d] => ret d s | _ => dom PTl end.
Definition rule_consp args s := match args with
 | [VCons _ _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PConsP end.
Definition rule_equal P args s := match args with
 | [a; b] => match kl_eq P (heap s) a b with
   | Some r => ret (VBool r) s | None => PDone (OWrong (kw "equality-undefined")) end
 | _ => dom PEqual end.
Definition rule_eval_kl args (s : store) := match args with
 | [d] => match parse [] d with Some e => PDone (OEval e) | None => throw XEvalKL end
 | _ => dom PEvalKL end.
Definition rule_absvector P args s := match args with
 | [VNum (NInt z)] => if Z.leb 0 z then
     if alloc_ok P (heap s) (Z.to_nat z)
     then ret (VVec (List.length (heap s)))
              (Store (heap s ++ [repeat (absvector_fill P) (Z.to_nat z)]) (gvals s) (gfuns s))
     else PDone (OFail RHeap)
   else dom PAbsvector
 | _ => dom PAbsvector end.
Definition rule_address_set args s := match args with
 | [VVec l; VNum (NInt z); x] => match nth_error (heap s) l with
   | Some cells => if (Z.leb 0 z && Z.ltb z (Z.of_nat (List.length cells)))%bool
     then ret (VVec l) (Store (replace_nth l (replace_nth (Z.to_nat z) x cells) (heap s)) (gvals s) (gfuns s))
     else throw XBounds
   | None => PDone (OWrong (kw "dangling-location")) end
 | _ => dom PAddressSet end.
Definition rule_address_get args s := match args with
 | [VVec l; VNum (NInt z)] => match nth_error (heap s) l with
   | Some cells => if Z.leb 0 z then match nth_error cells (Z.to_nat z) with
       | Some v => ret v s | None => throw XBounds end else throw XBounds
   | None => PDone (OWrong (kw "dangling-location")) end
 | _ => dom PAddressGet end.
Definition rule_absvectorp args s := match args with
 | [VVec _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PAbsvectorP end.

(* Environment interaction: the environment's response is an input label. *)
Definition io_fail (r : response) : pout := match r with
 | RFailed e => OThrow (XIO e) | _ => OThrow (XIO EProtocol) end.
Definition rule_write_byte args s := match args with
 | [VNum (NInt b); VStream h] => if (Z.leb 0 b && Z.ltb b 256)%bool
   then PIO (QWrite h [Z.to_N b]) (fun r => match r with
     | RWrote c => if N.eqb c 1 then ORet (VNum (NInt b)) s
                   else if N.eqb c 0 then OThrow (XIO EShortWrite) else OThrow (XIO EProtocol)
     | r => io_fail r end)
   else dom PWriteByte
 | _ => dom PWriteByte end.
Definition rule_read_byte args s := match args with
 | [VStream h] => PIO (QRead h 1) (fun r => match r with
   | RRead [b] => if N.ltb b 256 then ORet (VNum (NInt (Z.of_N b))) s else OThrow (XIO EProtocol)
   | RRead [] | REof => ORet (VNum (NInt (-1))) s
   | r => io_fail r end)
 | _ => dom PReadByte end.
Definition rule_open args s := match args with
 | [VStr path; VSym d] =>
   let go dir := PIO (QOpen path dir) (fun r => match r with
     | ROpened h => ORet (VStream h) s | r => io_fail r end) in
   if text_eqb d (kw "in") then go DIn else if text_eqb d (kw "out") then go DOut else dom POpen
 | _ => dom POpen end.
Definition rule_close args s := match args with
 | [VStream h] => PIO (QClose h) (fun r => match r with RClosed => ORet VNil s | r => io_fail r end)
 | _ => dom PClose end.
Definition rule_get_time P args s := match args with
 | [VSym k] => PIO (QTime k) (fun r => match r with
   | RTime z => match time_value P k z with Some n => ORet (VNum n) s | None => OThrow (XPrim PGetTime) end
   | r => io_fail r end)
 | _ => dom PGetTime end.

Definition rule_arith P p (iop : Z -> Z -> Z) args s := match args with
 | [VNum a; VNum b] => match int_or P p iop a b with Some n => ret (VNum n) s | None => dom p end
 | _ => dom p end.
Definition rule_div P args s := match args with
 | [VNum a; VNum b] => match num_div P a b with
   | None => throw XDivZero | Some (Some n) => ret (VNum n) s | Some None => dom PDiv end
 | _ => dom PDiv end.
Definition rule_cmp P p args s := match args with
 | [VNum a; VNum b] => ret (VBool (num_cmp P p a b)) s | _ => dom p end.
Definition rule_numberp args s := match args with
 | [VNum _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PNumberP end.

(* The complete primitive rule table: one named rule per primitive. *)
Definition prim_rule (P : profile) (p : prim) (args : list value) (s : store) : presult :=
 match p with
 | PIntern => rule_intern args s
 | PPos => rule_pos args s | PTlstr => rule_tlstr args s | PCn => rule_cn args s
 | PStr => rule_str P args s | PStringP => rule_stringp args s
 | PNToString => rule_n_to_string args s | PStringToN => rule_string_to_n args s
 | PSet => rule_set args s | PValue => rule_value args s
 | PSimpleError => rule_simple_error args s | PErrorToString => rule_error_to_string P args s
 | PCons => rule_cons args s | PHd => rule_hd args s | PTl => rule_tl args s | PConsP => rule_consp args s
 | PEqual => rule_equal P args s | PEvalKL => rule_eval_kl args s
 | PAbsvector => rule_absvector P args s | PAddressSet => rule_address_set args s
 | PAddressGet => rule_address_get args s | PAbsvectorP => rule_absvectorp args s
 | PWriteByte => rule_write_byte args s | PReadByte => rule_read_byte args s
 | POpen => rule_open args s | PClose => rule_close args s
 | PGetTime => rule_get_time P args s
 | PAdd => rule_arith P PAdd Z.add args s | PSub => rule_arith P PSub Z.sub args s
 | PMul => rule_arith P PMul Z.mul args s | PDiv => rule_div P args s
 | PGt => rule_cmp P PGt args s | PLt => rule_cmp P PLt args s
 | PGe => rule_cmp P PGe args s | PLe => rule_cmp P PLe args s
 | PNumberP => rule_numberp args s end.

(* ---------- machine ---------- *)
Inductive frame :=
 | KLet (x : name) (body : expr) (rho : lenv)
 | KIf (a b : expr) (rho : lenv)
 | KAnd (b : expr) (rho : lenv) | KAndR
 | KOr (b : expr) (rho : lenv) | KOrR
 | KCond (body : expr) (rest : list (expr * expr)) (rho : lenv)
 | KTrap (handler : expr) (rho : lenv)
 | KHead (args : list expr) (rho : lenv)
 | KArgs (f : value) (done : list value) (rest : list expr) (rho : lenv)
 | KCallArgs (f : name) (done : list value) (rest : list expr) (rho : lenv)
 | KApply (args : list value).

Inductive control :=
 | Eval (rho : lenv) (e : expr)
 | Ret (v : value)
 | Throw (x : exn)
 | Fail (r : resource)          (* modeled program resource failure *)
 | Halted (ev : env_event)      (* stopped by a signal or cancellation *)
 | Wrong (why : text).          (* operation undefined in the agreed profile *)

Record config := Cfg { ctl : control; kont : list frame; mem : store }.
Definition kl_outcome := outcome value exn.

Inductive move :=
 | MTau (c : config)
 | MIO (q : request) (k : response -> config)
 | MFinal (o : kl_outcome)
 | MWrong (why : text).

(* Pushing a frame is the only way the continuation grows; it is where the
   modeled stack bound is enforced. *)
Definition push (P : profile) (f : frame) (k : list frame) (c : control) (s : store) : config :=
 match stack_limit P with
 | Some n => if Nat.leb n (List.length k) then Cfg (Fail RStack) k s else Cfg c (f :: k) s
 | None => Cfg c (f :: k) s end.
(* Over-application: apply the result to remaining arguments, if any. *)
Definition continue_with P (rest : list value) (k : list frame) (c : control) (s : store) : config :=
 match rest with [] => Cfg c k s | _ => push P (KApply rest) k c s end.

Definition pout_config P (o : pout) (rest : list value) (k : list frame) (s : store) : config :=
 match o with
 | ORet v s' => continue_with P rest k (Ret v) s'
 | OThrow x => Cfg (Throw x) k s
 | OEval e => continue_with P rest k (Eval [] e) s
 | OFail r => Cfg (Fail r) k s
 | OWrong w => Cfg (Wrong w) k s end.

Definition prim_move P p args rest k s : move :=
 match prim_rule P p args s with
 | PDone o => MTau (pout_config P o rest k s)
 | PIO q kont => MIO q (fun r => pout_config P (kont r) rest k s) end.

(* Calls through the global function namespace: currying when too few
   arguments, exact call, or over-application of the result. Lookup happens at
   call time, so redefinition affects every later call. *)
Definition call_named P (g : name) (args : list value) (k : list frame) (s : store) : move :=
 match lookup g (gfuns s) with
 | None => MTau (Cfg (Throw (XUndefinedFun g)) k s)
 | Some (FUser ps body) =>
   if Nat.ltb (List.length args) (List.length ps) then MTau (Cfg (Ret (VPartial g args)) k s)
   else MTau (continue_with P (skipn (List.length ps) args) k
                (Eval (combine ps (firstn (List.length ps) args)) body) s)
 | Some (FPrim p) =>
   if Nat.ltb (List.length args) (prim_arity p) then MTau (Cfg (Ret (VPartial g args)) k s)
   else prim_move P p (firstn (prim_arity p) args) (skipn (prim_arity p) args) k s end.

(* Computed application of a value to a (possibly empty) argument list. *)
Definition apply_value P (f : value) (args : list value) (k : list frame) (s : store) : move :=
 match f, args with
 | VFrozen body rho, [] => MTau (Cfg (Eval rho body) k s)
 | VLam x body rho, a :: rest => MTau (continue_with P rest k (Eval ((x, a) :: rho) body) s)
 | VPartial g prev, _ => call_named P g (prev ++ args) k s
 | VFrozen _ _, _ :: _ | VLam _ _ _, [] => MTau (Cfg (Throw XArity) k s)
 | _, _ => MTau (Cfg (Throw XNotCallable) k s) end.

Fixpoint nodupb (l : list name) : bool := match l with
 | [] => true | x :: l => negb (bound l x) && nodupb l end.

Definition eval_move P (rho : lenv) (e : expr) (k : list frame) (s : store) : move :=
 match e with
 | ENum n => MTau (Cfg (Ret (VNum n)) k s)
 | EStr t => MTau (Cfg (Ret (VStr t)) k s)
 | ESym x => MTau (Cfg (Ret (VSym x)) k s)
 | EBool b => MTau (Cfg (Ret (VBool b)) k s)
 | ENil => MTau (Cfg (Ret VNil) k s)
 | EVar x => MTau (Cfg (match lookup x rho with Some v => Ret v | None => Throw (XUnboundVar x) end) k s)
 | ELam x b => MTau (Cfg (Ret (VLam x b rho)) k s)
 | EFreeze b => MTau (Cfg (Ret (VFrozen b rho)) k s)
 | ELet x a b => MTau (push P (KLet x b rho) k (Eval rho a) s)
 | EIf c a b => MTau (push P (KIf a b rho) k (Eval rho c) s)
 | EAnd a b => MTau (push P (KAnd b rho) k (Eval rho a) s)
 | EOr a b => MTau (push P (KOr b rho) k (Eval rho a) s)
 | ECond [] => MTau (Cfg (Throw XCondFail) k s)
 | ECond ((c, b) :: rest) => MTau (push P (KCond b rest rho) k (Eval rho c) s)
 | ETrap a h => MTau (push P (KTrap h rho) k (Eval rho a) s)
 | EType a => MTau (Cfg (Eval rho a) k s)
 | EDefun f ps b => if nodupb ps then
     MTau (Cfg (Ret (VSym f)) k (Store (heap s) (gvals s) ((f, FUser ps b) :: gfuns s)))
   else MTau (Cfg (Throw XBadDefinition) k s)
 | EApp h args => MTau (push P (KHead args rho) k (Eval rho h) s)
 | ECall f [] => call_named P f [] k s
 | ECall f (a :: rest) => MTau (push P (KCallArgs f [] rest rho) k (Eval rho a) s) end.

(* A value delivered to the innermost frame. Replacing one frame by another
   does not grow the continuation, so it needs no stack check. *)
Definition ret_move P (v : value) (f : frame) (k : list frame) (s : store) : move :=
 match f with
 | KLet x b rho => MTau (Cfg (Eval ((x, v) :: rho) b) k s)
 | KIf a b rho => MTau (Cfg (match v with
     | VBool true => Eval rho a | VBool false => Eval rho b | _ => Throw XNotBoolean end) k s)
 | KAnd b rho => match v with
     | VBool true => MTau (push P KAndR k (Eval rho b) s)
     | VBool false => MTau (Cfg (Ret (VBool false)) k s)
     | _ => MTau (Cfg (Throw XNotBoolean) k s) end
 | KOr b rho => match v with
     | VBool true => MTau (Cfg (Ret (VBool true)) k s)
     | VBool false => MTau (push P KOrR k (Eval rho b) s)
     | _ => MTau (Cfg (Throw XNotBoolean) k s) end
 | KAndR | KOrR => MTau (Cfg (match v with VBool b => Ret (VBool b) | _ => Throw XNotBoolean end) k s)
 | KCond b rest rho => MTau (Cfg (match v with
     | VBool true => Eval rho b | VBool false => Eval rho (ECond rest) | _ => Throw XNotBoolean end) k s)
 | KTrap _ _ => MTau (Cfg (Ret v) k s)
 | KHead [] rho => apply_value P v [] k s
 | KHead (a :: rest) rho => MTau (Cfg (Eval rho a) (KArgs v [] rest rho :: k) s)
 | KArgs fv done [] rho => apply_value P fv (rev (v :: done)) k s
 | KArgs fv done (a :: rest) rho => MTau (Cfg (Eval rho a) (KArgs fv (v :: done) rest rho :: k) s)
 | KCallArgs g done [] rho => call_named P g (rev (v :: done)) k s
 | KCallArgs g done (a :: rest) rho => MTau (Cfg (Eval rho a) (KCallArgs g (v :: done) rest rho :: k) s)
 | KApply args => apply_value P v args k s end.

(* Exceptions unwind one frame at a time; a trap frame evaluates its handler
   and applies it to the exception value. *)
Definition throw_move (x : exn) (f : frame) (k : list frame) (s : store) : move :=
 match f with
 | KTrap h rho => MTau (Cfg (Eval rho h) (KApply [VExn x] :: k) s)
 | _ => MTau (Cfg (Throw x) k s) end.

Definition next (P : profile) (c : config) : move :=
 match ctl c with
 | Eval rho e => eval_move P rho e (kont c) (mem c)
 | Ret v => match kont c with [] => MFinal (Normal v) | f :: k => ret_move P v f k (mem c) end
 | Throw x => match kont c with [] => MFinal (Error x) | f :: k => throw_move x f k (mem c) end
 | Fail r => MFinal (ResourceOut r)
 | Halted (Signal sg) => MFinal (Killed sg)
 | Halted Cancel => MFinal Cancelled
 | Wrong w => MWrong w end.

(* The open labeled step relation: internal steps, and IO steps that accept
   any environment response as their input label. *)
Inductive step (P : profile) : config -> label -> config -> Prop :=
 | step_tau c c' : next P c = MTau c' -> step P c Tau c'
 | step_io c q kk r : next P c = MIO q kk -> step P c (Obs (EvIO q r)) (kk r).
Definition final (P : profile) (c : config) (o : kl_outcome) := next P c = MFinal o.
Definition wrong (P : profile) (c : config) := exists w, next P c = MWrong w.
End KLSemantics.
