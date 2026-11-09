import LeanJit.KLValue
/-! Port of `rocq/KLSemantics.v`: small-step KLambda semantics. -/
namespace KLSemantics
open Observation KLSyntax KLSyntax.prim KLSyntax.expr KLValue KLValue.value KLValue.exn

-- ---------- eval-kl: data to resolved syntax ----------
def kw (s : String) : name := of_string s
def keyword (s : name) : Bool :=
  (["lambda", "let", "if", "and", "or", "cond", "trap-error", "defun", "freeze", "type"].map kw).any (text_eqb s)
def bound (scope : List name) (s : name) : Bool := scope.any (text_eqb s)
def symbols : value → Option (List name)
  | VNil => some []
  | VCons (VSym x) d => (symbols d).map (x :: ·)
  | _ => none

/- Rocq's inline `fix args` and `fix clauses` become mutual functions. -/
mutual
def parse (scope : List name) : value → Option expr
  | VNum n => some (ENum n) | VStr t => some (EStr t) | VBool b => some (EBool b) | VNil => some ENil
  | VSym s => some (if bound scope s then EVar s else ESym s)
  | VCons h t =>
    -- the non-keyword-head case, bound before the match so the recursion stays structural
    let other := match parse scope h, parse_args scope t with
      | some eh, some es => some (EApp eh es) | _, _ => none
    match h with
    | VSym s =>
      if text_eqb s (kw "lambda") then match t with
        | VCons (VSym x) (VCons b VNil) => (parse (x :: scope) b).map (ELam x) | _ => none
      else if text_eqb s (kw "let") then match t with
        | VCons (VSym x) (VCons a (VCons b VNil)) => match parse scope a, parse (x :: scope) b with
          | some ea, some eb => some (ELet x ea eb) | _, _ => none
        | _ => none
      else if text_eqb s (kw "if") then match t with
        | VCons c (VCons a (VCons b VNil)) => match parse scope c, parse scope a, parse scope b with
          | some ec, some ea, some eb => some (EIf ec ea eb) | _, _, _ => none
        | _ => none
      else if text_eqb s (kw "and") then match t with
        | VCons a (VCons b VNil) => match parse scope a, parse scope b with
          | some ea, some eb => some (EAnd ea eb) | _, _ => none
        | _ => none
      else if text_eqb s (kw "or") then match t with
        | VCons a (VCons b VNil) => match parse scope a, parse scope b with
          | some ea, some eb => some (EOr ea eb) | _, _ => none
        | _ => none
      else if text_eqb s (kw "cond") then (parse_clauses scope t).map ECond
      else if text_eqb s (kw "trap-error") then match t with
        | VCons a (VCons b VNil) => match parse scope a, parse scope b with
          | some ea, some eb => some (ETrap ea eb) | _, _ => none
        | _ => none
      else if text_eqb s (kw "defun") then match t with
        | VCons (VSym f) (VCons ps (VCons b VNil)) => match symbols ps with
          | some xs => (parse xs b).map (EDefun f xs) | none => none
        | _ => none
      else if text_eqb s (kw "freeze") then match t with
        | VCons a VNil => (parse scope a).map EFreeze | _ => none
      else if text_eqb s (kw "type") then match t with
        | VCons a (VCons _ VNil) => (parse scope a).map EType | _ => none
      else if bound scope s then (parse_args scope t).map (EApp (EVar s))
      else (parse_args scope t).map (ECall s)
    | _ => other
  | _ => none
def parse_args (scope : List name) : value → Option (List expr)
  | VNil => some []
  | VCons a d => match parse scope a, parse_args scope d with
    | some e, some es => some (e :: es) | _, _ => none
  | _ => none
def parse_clauses (scope : List name) : value → Option (List (expr × expr))
  | VNil => some []
  | VCons (VCons c (VCons b VNil)) more => match parse scope c, parse scope b, parse_clauses scope more with
    | some ec, some eb, some cs => some ((ec, eb) :: cs) | _, _, _ => none
  | _ => none
end

-- ---------- primitive rules ----------
inductive pout
  | ORet (v : value) (s : store)
  | OThrow (x : exn)
  | OEval (e : expr)
  | OFail (r : resource)
  | OWrong (why : text)
inductive presult | PDone (o : pout) | PIO (q : request) (k : response → pout)
open pout presult

def ret (v : value) (s : store) := PDone (ORet v s)
def throw (x : exn) := PDone (OThrow x)
def dom (p : prim) := PDone (OThrow (XPrim p))

def rule_intern (args : List value) (s : store) := match args with
  | [VStr t] => ret (if text_eqb t (kw "true") then VBool true
                     else if text_eqb t (kw "false") then VBool false else VSym t) s
  | _ => dom PIntern
def rule_pos (args : List value) (s : store) := match args with
  | [VStr t, VNum (.NInt z)] => if decide (0 ≤ z) && decide (z < (t.length : Int))
      then match t[z.toNat]? with | some c => ret (VStr [c]) s | none => throw XBounds
      else throw XBounds
  | _ => dom PPos
def rule_tlstr (args : List value) (s : store) := match args with
  | [VStr (_ :: t)] => ret (VStr t) s | [VStr []] => throw XBounds | _ => dom PTlstr
def rule_cn (args : List value) (s : store) := match args with
  | [VStr a, VStr b] => ret (VStr (a ++ b)) s | _ => dom PCn
def rule_str (P : profile) (args : List value) (s : store) := match args with
  | [VNum (.NInt z)] => ret (VStr (dec_text z)) s
  | [VNum (.NFloat f)] => ret (VStr (P.float_text f)) s
  | [VSym x] => ret (VStr x) s
  | [VBool b] => ret (VStr (bool_text b)) s
  | [v] => match P.str_other v with | some t => ret (VStr t) s | none => dom PStr
  | _ => dom PStr
def rule_stringp (args : List value) (s : store) := match args with
  | [VStr _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PStringP
def rule_n_to_string (args : List value) (s : store) := match args with
  | [VNum (.NInt z)] => if scalar_ok z then ret (VStr [z.toNat]) s else dom PNToString
  | _ => dom PNToString
def rule_string_to_n (args : List value) (s : store) := match args with
  | [VStr (c :: _)] => ret (VNum (.NInt (c : Int))) s | [VStr []] => throw XBounds
  | _ => dom PStringToN
def rule_set (args : List value) (s : store) := match args with
  | [VSym x, v] => ret v ⟨s.heap, (x, v) :: s.gvals, s.gfuns⟩
  | _ => dom PSet
def rule_value (args : List value) (s : store) := match args with
  | [VSym x] => match lookup x s.gvals with | some v => ret v s | none => throw (XUnboundGlobal x)
  | _ => dom PValue
def rule_simple_error (args : List value) (_s : store) := match args with
  | [VStr t] => throw (XUser t) | _ => dom PSimpleError
def rule_error_to_string (P : profile) (args : List value) (s : store) := match args with
  | [VExn (XUser t)] => ret (VStr t) s
  | [VExn x] => ret (VStr (P.sys_message x)) s
  | _ => dom PErrorToString
def rule_cons (args : List value) (s : store) := match args with | [a, b] => ret (VCons a b) s | _ => dom PCons
def rule_hd (args : List value) (s : store) := match args with | [VCons a _] => ret a s | _ => dom PHd
def rule_tl (args : List value) (s : store) := match args with | [VCons _ d] => ret d s | _ => dom PTl
def rule_consp (args : List value) (s : store) := match args with
  | [VCons _ _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PConsP
def rule_equal (P : profile) (args : List value) (s : store) := match args with
  | [a, b] => match kl_eq P s.heap a b with
    | some r => ret (VBool r) s | none => PDone (OWrong (kw "equality-undefined"))
  | _ => dom PEqual
def rule_eval_kl (args : List value) (_s : store) := match args with
  | [d] => match parse [] d with | some e => PDone (OEval e) | none => throw XEvalKL
  | _ => dom PEvalKL
def rule_absvector (P : profile) (args : List value) (s : store) := match args with
  | [VNum (.NInt z)] => if decide (0 ≤ z) then
      if alloc_ok P s.heap z.toNat
      then ret (VVec s.heap.length) ⟨s.heap ++ [List.replicate z.toNat P.absvector_fill], s.gvals, s.gfuns⟩
      else PDone (OFail .RHeap)
    else dom PAbsvector
  | _ => dom PAbsvector
def rule_address_set (args : List value) (s : store) := match args with
  | [VVec l, VNum (.NInt z), x] => match s.heap[l]? with
    | some cells => if decide (0 ≤ z) && decide (z < (cells.length : Int))
      then ret (VVec l) ⟨replace_nth l (replace_nth z.toNat x cells) s.heap, s.gvals, s.gfuns⟩
      else throw XBounds
    | none => PDone (OWrong (kw "dangling-location"))
  | _ => dom PAddressSet
def rule_address_get (args : List value) (s : store) := match args with
  | [VVec l, VNum (.NInt z)] => match s.heap[l]? with
    | some cells => if decide (0 ≤ z) then match cells[z.toNat]? with
        | some v => ret v s | none => throw XBounds else throw XBounds
    | none => PDone (OWrong (kw "dangling-location"))
  | _ => dom PAddressGet
def rule_absvectorp (args : List value) (s : store) := match args with
  | [VVec _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PAbsvectorP

def io_fail (r : response) : pout := match r with
  | .RFailed e => OThrow (XIO e) | _ => OThrow (XIO .EProtocol)
def rule_write_byte (args : List value) (s : store) := match args with
  | [VNum (.NInt b), VStream h] => if decide (0 ≤ b) && decide (b < 256)
    then PIO (.QWrite h [b.toNat]) (fun r => match r with
      | .RWrote c => if c == 1 then ORet (VNum (.NInt b)) s
                     else if c == 0 then OThrow (XIO .EShortWrite) else OThrow (XIO .EProtocol)
      | r => io_fail r)
    else dom PWriteByte
  | _ => dom PWriteByte
def rule_read_byte (args : List value) (s : store) := match args with
  | [VStream h] => PIO (.QRead h 1) (fun r => match r with
    | .RRead [b] => if decide (b < 256) then ORet (VNum (.NInt (b : Int))) s else OThrow (XIO .EProtocol)
    | .RRead [] | .REof => ORet (VNum (.NInt (-1))) s
    | r => io_fail r)
  | _ => dom PReadByte
def rule_open (args : List value) (s : store) := match args with
  | [VStr path, VSym d] =>
    let go dir := PIO (.QOpen path dir) (fun r => match r with
      | .ROpened h => ORet (VStream h) s | r => io_fail r)
    if text_eqb d (kw "in") then go .DIn else if text_eqb d (kw "out") then go .DOut else dom POpen
  | _ => dom POpen
def rule_close (args : List value) (s : store) := match args with
  | [VStream h] => PIO (.QClose h) (fun r => match r with | .RClosed => ORet VNil s | r => io_fail r)
  | _ => dom PClose
def rule_get_time (P : profile) (args : List value) (s : store) := match args with
  | [VSym k] => PIO (.QTime k) (fun r => match r with
    | .RTime z => match P.time_value k z with | some n => ORet (VNum n) s | none => OThrow (XPrim PGetTime)
    | r => io_fail r)
  | _ => dom PGetTime

def rule_arith (P : profile) (p : prim) (iop : Int → Int → Int) (args : List value) (s : store) :=
  match args with
  | [VNum a, VNum b] => match int_or P p iop a b with | some n => ret (VNum n) s | none => dom p
  | _ => dom p
def rule_div (P : profile) (args : List value) (s : store) := match args with
  | [VNum a, VNum b] => match num_div P a b with
    | none => throw XDivZero | some (some n) => ret (VNum n) s | some none => dom PDiv
  | _ => dom PDiv
def rule_cmp (P : profile) (p : prim) (args : List value) (s : store) := match args with
  | [VNum a, VNum b] => ret (VBool (num_cmp P p a b)) s | _ => dom p
def rule_numberp (args : List value) (s : store) := match args with
  | [VNum _] => ret (VBool true) s | [_] => ret (VBool false) s | _ => dom PNumberP

def prim_rule (P : profile) (p : prim) (args : List value) (s : store) : presult :=
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
  | PAdd => rule_arith P PAdd (· + ·) args s | PSub => rule_arith P PSub (· - ·) args s
  | PMul => rule_arith P PMul (· * ·) args s | PDiv => rule_div P args s
  | PGt => rule_cmp P PGt args s | PLt => rule_cmp P PLt args s
  | PGe => rule_cmp P PGe args s | PLe => rule_cmp P PLe args s
  | PNumberP => rule_numberp args s

-- ---------- machine ----------
inductive frame
  | KLet (x : name) (body : expr) (rho : lenv)
  | KIf (a b : expr) (rho : lenv)
  | KAnd (b : expr) (rho : lenv) | KAndR
  | KOr (b : expr) (rho : lenv) | KOrR
  | KCond (body : expr) (rest : List (expr × expr)) (rho : lenv)
  | KTrap (handler : expr) (rho : lenv)
  | KHead (args : List expr) (rho : lenv)
  | KArgs (f : value) (done : List value) (rest : List expr) (rho : lenv)
  | KCallArgs (f : name) (done : List value) (rest : List expr) (rho : lenv)
  | KApply (args : List value)
open frame

inductive control
  | Eval (rho : lenv) (e : expr)
  | Ret (v : value)
  | Throw (x : exn)
  | Fail (r : resource)
  | Halted (ev : env_event)
  | Wrong (why : text)
open control

structure config where
  Cfg ::
  ctl : control
  kont : List frame
  mem : store
open config (Cfg)
abbrev kl_outcome := outcome value exn

inductive move
  | MTau (c : config)
  | MIO (q : request) (k : response → config)
  | MFinal (o : kl_outcome)
  | MWrong (why : text)
open move

def push (P : profile) (f : frame) (k : List frame) (c : control) (s : store) : config :=
  match P.stack_limit with
  | some n => if decide (n ≤ k.length) then Cfg (Fail .RStack) k s else Cfg c (f :: k) s
  | none => Cfg c (f :: k) s
def continue_with (P : profile) (rest : List value) (k : List frame) (c : control) (s : store) : config :=
  match rest with | [] => Cfg c k s | _ => push P (KApply rest) k c s

def pout_config (P : profile) (o : pout) (rest : List value) (k : List frame) (s : store) : config :=
  match o with
  | ORet v s' => continue_with P rest k (Ret v) s'
  | OThrow x => Cfg (Throw x) k s
  | OEval e => continue_with P rest k (Eval [] e) s
  | OFail r => Cfg (Fail r) k s
  | OWrong w => Cfg (Wrong w) k s

def prim_move (P : profile) (p : prim) (args rest : List value) (k : List frame) (s : store) : move :=
  match prim_rule P p args s with
  | PDone o => MTau (pout_config P o rest k s)
  | PIO q kont => MIO q (fun r => pout_config P (kont r) rest k s)

def call_named (P : profile) (g : name) (args : List value) (k : List frame) (s : store) : move :=
  match lookup g s.gfuns with
  | none => MTau (Cfg (Throw (XUndefinedFun g)) k s)
  | some (.FUser ps body) =>
    if decide (args.length < ps.length) then MTau (Cfg (Ret (VPartial g args)) k s)
    else MTau (continue_with P (args.drop ps.length) k (Eval (ps.zip (args.take ps.length)) body) s)
  | some (.FPrim p) =>
    if decide (args.length < prim_arity p) then MTau (Cfg (Ret (VPartial g args)) k s)
    else prim_move P p (args.take (prim_arity p)) (args.drop (prim_arity p)) k s

def apply_value (P : profile) (f : value) (args : List value) (k : List frame) (s : store) : move :=
  match f, args with
  | VFrozen body rho, [] => MTau (Cfg (Eval rho body) k s)
  | VLam x body rho, a :: rest => MTau (continue_with P rest k (Eval ((x, a) :: rho) body) s)
  | VPartial g prev, _ => call_named P g (prev ++ args) k s
  | VFrozen _ _, _ :: _ | VLam _ _ _, [] => MTau (Cfg (Throw XArity) k s)
  | _, _ => MTau (Cfg (Throw XNotCallable) k s)

def nodupb : List name → Bool
  | [] => true
  | x :: l => !(bound l x) && nodupb l

def eval_move (P : profile) (rho : lenv) (e : expr) (k : List frame) (s : store) : move :=
  match e with
  | ENum n => MTau (Cfg (Ret (VNum n)) k s)
  | EStr t => MTau (Cfg (Ret (VStr t)) k s)
  | ESym x => MTau (Cfg (Ret (VSym x)) k s)
  | EBool b => MTau (Cfg (Ret (VBool b)) k s)
  | ENil => MTau (Cfg (Ret VNil) k s)
  | EVar x => MTau (Cfg (match lookup x rho with | some v => Ret v | none => Throw (XUnboundVar x)) k s)
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
      MTau (Cfg (Ret (VSym f)) k ⟨s.heap, s.gvals, (f, .FUser ps b) :: s.gfuns⟩)
    else MTau (Cfg (Throw XBadDefinition) k s)
  | EApp h args => MTau (push P (KHead args rho) k (Eval rho h) s)
  | ECall f [] => call_named P f [] k s
  | ECall f (a :: rest) => MTau (push P (KCallArgs f [] rest rho) k (Eval rho a) s)

def ret_move (P : profile) (v : value) (f : frame) (k : List frame) (s : store) : move :=
  match f with
  | KLet x b rho => MTau (Cfg (Eval ((x, v) :: rho) b) k s)
  | KIf a b rho => MTau (Cfg (match v with
      | VBool true => Eval rho a | VBool false => Eval rho b | _ => Throw XNotBoolean) k s)
  | KAnd b rho => match v with
      | VBool true => MTau (push P KAndR k (Eval rho b) s)
      | VBool false => MTau (Cfg (Ret (VBool false)) k s)
      | _ => MTau (Cfg (Throw XNotBoolean) k s)
  | KOr b rho => match v with
      | VBool true => MTau (Cfg (Ret (VBool true)) k s)
      | VBool false => MTau (push P KOrR k (Eval rho b) s)
      | _ => MTau (Cfg (Throw XNotBoolean) k s)
  | KAndR | KOrR => MTau (Cfg (match v with | VBool b => Ret (VBool b) | _ => Throw XNotBoolean) k s)
  | KCond b rest rho => MTau (Cfg (match v with
      | VBool true => Eval rho b | VBool false => Eval rho (ECond rest) | _ => Throw XNotBoolean) k s)
  | KTrap _ _ => MTau (Cfg (Ret v) k s)
  | KHead [] _ => apply_value P v [] k s
  | KHead (a :: rest) rho => MTau (Cfg (Eval rho a) (KArgs v [] rest rho :: k) s)
  | KArgs fv done [] _ => apply_value P fv (v :: done).reverse k s
  | KArgs fv done (a :: rest) rho => MTau (Cfg (Eval rho a) (KArgs fv (v :: done) rest rho :: k) s)
  | KCallArgs g done [] _ => call_named P g (v :: done).reverse k s
  | KCallArgs g done (a :: rest) rho => MTau (Cfg (Eval rho a) (KCallArgs g (v :: done) rest rho :: k) s)
  | KApply args => apply_value P v args k s

def throw_move (x : exn) (f : frame) (k : List frame) (s : store) : move :=
  match f with
  | KTrap h rho => MTau (Cfg (Eval rho h) (KApply [VExn x] :: k) s)
  | _ => MTau (Cfg (Throw x) k s)

def next (P : profile) (c : config) : move :=
  match c.ctl with
  | Eval rho e => eval_move P rho e c.kont c.mem
  | Ret v => match c.kont with | [] => MFinal (.Normal v) | f :: k => ret_move P v f k c.mem
  | Throw x => match c.kont with | [] => MFinal (.Error x) | f :: k => throw_move x f k c.mem
  | Fail r => MFinal (.ResourceOut r)
  | Halted (.Signal sg) => MFinal (.Killed sg)
  | Halted .Cancel => MFinal .Cancelled
  | Wrong w => MWrong w

inductive step (P : profile) : config → label → config → Prop
  | step_tau c c' : next P c = MTau c' → step P c .Tau c'
  | step_io c q kk r : next P c = MIO q kk → step P c (.Obs (.EvIO q r)) (kk r)
def final (P : profile) (c : config) (o : kl_outcome) := next P c = MFinal o
def wrong (P : profile) (c : config) := ∃ w, next P c = MWrong w

end KLSemantics
