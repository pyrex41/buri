(* Port of rocq/JitBytecode.v: an executable semantics of Shen/JIT's register bytecode at pin
   d3348ce (0.4). `next` is a function, so one state has one move.
   Encoding notes:
   - positive is F* pos; the finite map `tree` recurses on k/2 (xO k = 2k, xI k = 2k+1).
   - Rocq's `Eval vm_compute in sym "move"` constants are plain definitions here; the normalizer
     computes them where they are used.
   - `prim_step`'s Rocq match on (primitive, argument shape) with a final catch-all is a match on
     the primitive, then on the argument shape, each mismatch going to the same catch-all
     (`prim_fallback`). Each primitive occurs in exactly one Rocq branch, so the two agree.
   - Machine-record updates use F*'s { m with ... } in place of Rocq's set_* records; the set_*
     names are kept. *)
module Buri.JitBytecode
open Buri.Lib
open Buri.JitFloat

type text = list nat
let t (s : string) : text = of_string s

(* ---------- finite maps ---------- *)
type tree (a : Type) = | Leaf : tree a | Node : l:tree a -> v:option a -> r:tree a -> tree a

let rec tget (#a : Type) (k : pos) (m : tree a) : Tot (option a) (decreases k) =
  match m with
  | Leaf -> None
  | Node l v r -> if k = 1 then v else if k % 2 = 0 then tget (k / 2) l else tget (k / 2) r

let rec tset (#a : Type) (k : pos) (x : a) (m : tree a) : Tot (tree a) (decreases k) =
  match m with
  | Leaf ->
    if k = 1 then Node Leaf (Some x) Leaf
    else if k % 2 = 0 then Node (tset (k / 2) x Leaf) None Leaf
    else Node Leaf None (tset (k / 2) x Leaf)
  | Node l v r ->
    if k = 1 then Node l (Some x) r
    else if k % 2 = 0 then Node (tset (k / 2) x l) v r
    else Node l v (tset (k / 2) x r)

(* ---------- symbols ---------- *)
let sym_of_text (s : text) : pos =
  fold_left #pos #nat (fun acc b -> acc * 256 + (if b = 0 then 256 else b)) s 1
let sym (s : string) : pos = sym_of_text (t s)
let s_move : pos = sym "move"
let s_const : pos = sym "const"
let s_capture : pos = sym "capture"
let s_closure : pos = sym "closure"
let s_prim : pos = sym "prim"
let s_label : pos = sym "label"
let s_jump : pos = sym "jump"
let s_jump_if_false : pos = sym "jump-if-false"
let s_call : pos = sym "call"
let s_call_sealed : pos = sym "call-sealed"
let s_call_value : pos = sym "call-value"
let s_tail_call : pos = sym "tail-call"
let s_tail_call_sealed : pos = sym "tail-call-sealed"
let s_tail_call_value : pos = sym "tail-call-value"
let s_return : pos = sym "return"
let s_push_handler : pos = sym "push-handler"
let s_pop_handler : pos = sym "pop-handler"
let s_exception : pos = sym "exception"
let s_entry : pos = sym "entry"
let s_jump_unless_entry : pos = sym "jump-unless-entry"
let s_inline : pos = sym "inline"
let s_code : pos = sym "code"
let s_defun : pos = sym "defun"
let s_run : pos = sym "run"
let s_unix : pos = sym "unix"
let s_in : pos = sym "in"
let s_out : pos = sym "out"
let s_shen_fail_ : pos = sym "shen.fail!"
let s__home_directory_ : pos = sym "*home-directory*"

let rec text_of_sym_go (fuel : nat) (p : int) (acc : text) : Tot text (decreases fuel) =
  if fuel = 0 then acc
  else if p <= 1 then acc else
    let d = zrem (p - 1) 256 + 1 in
    text_of_sym_go (fuel - 1) (zquot (p - d) 256) (to_nat (zrem d 256) :: acc)
let text_of_sym (p : pos) : text = text_of_sym_go 4096 p []

(* ---------- values, code, heap ---------- *)
type val_ =
  | VFix : z:int -> val_
  | VReal : bits:nat -> val_
  | VSym : s:pos -> val_
  | VBool : b:bool -> val_
  | VNil : val_
  | VCleared : val_
  | VStr : s:text -> val_
  | VPair : a:val_ -> d:val_ -> val_
  | VVec : l:pos -> val_
  | VBytes : l:pos -> val_
  | VClo : l:pos -> val_
  | VExn : l:pos -> val_
  | VStream : l:pos -> val_
  | VPvar : off:int -> val_

type prim =
  | PAdd | PSub | PMul | PDiv | PLt | PGt | PLe | PGe | PEq | PNumberp
  | PCons | PHd | PTl | PConsp | PCn | PPos | PTlstr | PStr | PStringp
  | PNString | PStringN | PIntern | PAbsvector | PAbsvectorp
  | PGetAddress | PSetAddress | PSet | PValue | PSimpleError
  | PErrorToString | PEvalKl | PGetTime | POpen | PClose | PReadByte
  | PWriteByte | PCharStreamp | PReadUnitString | PWriteString
  | PInstall | PSymbolp | PHash | PExit | PSymbolKind | PFilledVector
  | PDictFind | PDictPut | PDictRemove | PDictEntries | PTaggedp
  | PSealedp | PSealing | PInlineBody | PVectorp | PAbsvector3 | PQuietp
  | PMarkToplevel | PTraceText | PBacktrace | PReadFile | PIntegerp | PAppend
  | PArityp | PInlinedp | PSaveExecutable
  | PBytesNew | PBytesp | PBytesLength | PU8 | PU16 | PU32 | PSetU8 | PSetU16 | PSetU32
  | PStringBytes | PBytesString | PCopyBytes
  | PBitAnd | PBitOr | PBitXor | PBitNot | PShiftLeft | PShiftRight
  | PRotate32 | PBswap32 | PPopcount | PClz | PCtz | PDecimal
  | PPvar | PPvarp | PPvarOffset | PDeref | PSamep
  | PThread | PForeign | PPointerp | PPointerKind | PPointerAddress | PBytesPointer
  | PPointerString | PPointerBytes | PErrno | PCErrno | PPointerKill
  | PS32 | PS64 | PF32 | PF64 | PSetS32 | PSetS64 | PSetF32 | PSetF64
  | PPointerSized | PSetPointer | PPointerGuard | PPointerOwner | PPointersDead | PPointerReadOnly
  | PCollect
  | PRaiseCond

let prim_table : list (string & prim & nat) =
 [("+",PAdd,2);("-",PSub,2);("*",PMul,2);("/",PDiv,2);("<",PLt,2);(">",PGt,2);("<=",PLe,2);(">=",PGe,2)
 ;("=",PEq,2);("number?",PNumberp,1);("cons",PCons,2);("hd",PHd,1);("tl",PTl,1);("cons?",PConsp,1)
 ;("cn",PCn,2);("pos",PPos,2);("tlstr",PTlstr,1);("str",PStr,1);("string?",PStringp,1)
 ;("n->string",PNString,1);("string->n",PStringN,1);("intern",PIntern,1);("absvector",PAbsvector,1)
 ;("absvector?",PAbsvectorp,1);("<-address",PGetAddress,2);("address->",PSetAddress,3);("set",PSet,2)
 ;("value",PValue,1);("simple-error",PSimpleError,1);("error-to-string",PErrorToString,1)
 ;("eval-kl",PEvalKl,1);("get-time",PGetTime,1);("open",POpen,2);("close",PClose,1)
 ;("read-byte",PReadByte,1);("write-byte",PWriteByte,2);("char-stream?",PCharStreamp,1)
 ;("read-unit-string",PReadUnitString,1);("write-string",PWriteString,2)
 ;("shen-jit.install",PInstall,1);("shen-jit.symbol?",PSymbolp,1);("shen-jit.hash",PHash,2)
 ;("shen-jit.exit",PExit,1);("shen-jit.symbol-kind",PSymbolKind,1)
 ;("shen-jit.filled-vector",PFilledVector,2);("shen-jit.dict-find",PDictFind,2)
 ;("shen-jit.dict-put",PDictPut,3);("shen-jit.dict-remove",PDictRemove,2)
 ;("shen-jit.dict-entries",PDictEntries,1);("shen-jit.tagged?",PTaggedp,2)
 ;("shen-jit.sealed?",PSealedp,1);("shen-jit.sealing",PSealing,1);("shen-jit.inline-body",PInlineBody,1)
 ;("shen-jit.vector?",PVectorp,1);("shen-jit.absvector3",PAbsvector3,3);("shen-jit.quiet?",PQuietp,0)
 ;("shen-jit.mark-toplevel",PMarkToplevel,0);("shen-jit.trace-text",PTraceText,1)
 ;("shen-jit.backtrace",PBacktrace,0);("shen-jit.read-file",PReadFile,2);("shen-jit.integer?",PIntegerp,1)
 ;("shen-jit.append",PAppend,2);("shen-jit.arity?",PArityp,2);("shen-jit.inlined?",PInlinedp,2)
 ;("shen-jit.save-executable",PSaveExecutable,2);("shen-jit.bytes",PBytesNew,1);("shen-jit.bytes?",PBytesp,1)
 ;("shen-jit.bytes-length",PBytesLength,1);("shen-jit.u8",PU8,2);("shen-jit.u16",PU16,2);("shen-jit.u32",PU32,2)
 ;("shen-jit.u8!",PSetU8,3);("shen-jit.u16!",PSetU16,3);("shen-jit.u32!",PSetU32,3)
 ;("shen-jit.s32",PS32,2);("shen-jit.s64",PS64,2);("shen-jit.f32",PF32,2);("shen-jit.f64",PF64,2)
 ;("shen-jit.s32!",PSetS32,3);("shen-jit.s64!",PSetS64,3);("shen-jit.f32!",PSetF32,3);("shen-jit.f64!",PSetF64,3)
 ;("shen-jit.string->bytes",PStringBytes,1);("shen-jit.bytes->string",PBytesString,3)
 ;("shen-jit.copy-bytes",PCopyBytes,5);("shen-jit.bit-and",PBitAnd,2);("shen-jit.bit-or",PBitOr,2)
 ;("shen-jit.bit-xor",PBitXor,2);("shen-jit.bit-not",PBitNot,1);("shen-jit.shift-left",PShiftLeft,2)
 ;("shen-jit.shift-right",PShiftRight,2);("shen-jit.rotate32",PRotate32,2);("shen-jit.bswap32",PBswap32,1)
 ;("shen-jit.popcount",PPopcount,1);("shen-jit.clz",PClz,1);("shen-jit.ctz",PCtz,1);("shen-jit.decimal",PDecimal,2)
 ;("shen-jit.pvar",PPvar,1);("shen-jit.pvar?",PPvarp,1);("shen-jit.pvar-offset",PPvarOffset,1)
 ;("shen-jit.deref",PDeref,3);("shen-jit.same?",PSamep,2);("shen-jit.thread",PThread,1)
 ;("shen-jit.foreign",PForeign,2);("shen-jit.pointer?",PPointerp,1);("shen-jit.pointer-kind",PPointerKind,1)
 ;("shen-jit.pointer-address",PPointerAddress,1);("shen-jit.bytes->pointer",PBytesPointer,3)
 ;("shen-jit.pointer->string",PPointerString,1);("shen-jit.pointer->bytes",PPointerBytes,3)
 ;("shen-jit.errno",PErrno,0);("shen-jit.c-errno",PCErrno,0);("shen-jit.pointer-kill",PPointerKill,1)
 ;("shen-jit.pointer-sized",PPointerSized,2);("shen-jit.pointer!",PSetPointer,3)
 ;("shen-jit.pointer-guard",PPointerGuard,2);("shen-jit.pointer-owner",PPointerOwner,1)
 ;("shen-jit.pointers-dead",PPointersDead,0);("shen-jit.pointer-read-only",PPointerReadOnly,1)
 ;("shen-jit.collect",PCollect,0)
 ;("raise-cond",PRaiseCond,0)]

type operand = | OSlot : s:nat -> operand | OConst : k:nat -> operand
type instr =
  | IMove : d:nat -> s:nat -> instr
  | IConst : d:nat -> k:nat -> instr
  | ICapture : d:nat -> i:nat -> instr
  | IClosure : d:nat -> c:nat -> ss:list nat -> instr
  | IPrim : d:nat -> p:prim -> ops:list operand -> instr
  | ILabel : l:nat -> instr
  | IJump : l:nat -> instr
  | IJumpIfFalse : o:operand -> l:nat -> instr
  | ICall : d:nat -> a:nat -> f:pos -> n:nat -> instr
  | ICallSealed : d:nat -> a:nat -> f:pos -> n:nat -> instr
  | ICallValue : d:nat -> a:nat -> n:nat -> instr
  | ITail : a:nat -> f:pos -> n:nat -> instr
  | ITailSealed : a:nat -> f:pos -> n:nat -> instr
  | ITailValue : a:nat -> n:nat -> instr
  | IReturn : o:operand -> instr
  | IPushHandler : l:nat -> instr
  | IPopHandler : instr
  | IException : d:nat -> instr
  | IEntry : n:nat -> l:nat -> instr
  | IJumpUnlessEntry : s:nat -> n:nat -> l:nat -> instr
  | IInline : f:pos -> n:nat -> instr

type code =
  | Code : c_name:val_ -> c_arity:nat -> c_entry:option (nat & nat) -> c_frame:nat ->
           c_consts:list val_ -> c_ins:list instr -> c_codes:list code -> c_inline:val_ -> code
let code_name (c : code) = match c with Code x _ _ _ _ _ _ _ -> x
let code_arity (c : code) = match c with Code _ x _ _ _ _ _ _ -> x
let code_entry (c : code) = match c with Code _ _ x _ _ _ _ _ -> x
let code_frame (c : code) = match c with Code _ _ _ x _ _ _ _ -> x
let code_consts (c : code) = match c with Code _ _ _ _ x _ _ _ -> x
let code_ins (c : code) = match c with Code _ _ _ _ _ x _ _ -> x
let code_codes (c : code) = match c with Code _ _ _ _ _ _ x _ -> x
let code_inline (c : code) = match c with Code _ _ _ _ _ _ _ x -> x

type stream_dir = | SIn | SOut
type obj =
  | OVec : cells:list val_ -> obj
  | OBytes : bs:list nat -> obj
  | OClo : c:code -> caps:list val_ -> obj
  | OExn : msg:text -> v:val_ -> obj
  | OStream : handle:nat -> d:stream_dir -> is_open:bool -> obj

type cont = { k_code : code; k_rest : list instr; k_dst : nat; k_window : nat }
let mkCont c r d a : cont = { k_code = c; k_rest = r; k_dst = d; k_window = a }
type handler = { h_code : code; h_label : nat; h_fp : nat; h_conts : list cont; h_quiet : bool }

type machine = {
  m_stack : tree val_; m_fp : nat; m_code : code; m_rest : list instr;
  m_conts : list cont; m_handlers : list handler; m_exn : val_;
  m_heap : tree obj; m_next : pos;
  m_gval : tree val_; m_gfun : tree val_; m_sealed : tree unit; m_seal_user : bool;
  m_allocs : nat }

noeq type env = { e_oom : nat -> bool; e_stack : nat -> bool; e_hash : text -> int }

type jreq =
  | JOpen : path:text -> d:stream_dir -> jreq | JClose : h:nat -> jreq
  | JRead : h:nat -> jreq | JWrite : h:nat -> b:nat -> jreq | JTime : run:bool -> jreq
  | JReadFile : path:text -> jreq
type jres =
  | JOpened : h:nat -> jres | JFailed | JDone | JByte : b:nat -> jres | JEof
  | JTimeIs : bits:nat -> jres | JFile : bs:list nat -> jres

type stuck =
  | RBadSlot : s:nat -> stuck
  | RBadConst | RBadLabel | RFallOff | RBadCapture | RBadCode
  | RIdentity
  | RCyclic
  | RExcluded : p:prim -> stuck
  | RArgs

type final = | FReturn : v:val_ -> final | FError : e:val_ -> final | FExit : status:int -> final
noeq type move =
  | MTau : m:machine -> move
  | MIO : q:jreq -> k:(jres -> machine) -> move
  | MFinal : o:final -> m:machine -> move
  | MStuck : why:stuck -> move

(* ---------- small helpers ---------- *)
let skey (n : nat) : pos = succ_pos n
let sread (m : machine) (s : nat) : option val_ = tget (skey (m.m_fp + s)) m.m_stack
let swrite (m : machine) (s : nat) (v : val_) : tree val_ = tset (skey (m.m_fp + s)) v m.m_stack
let set_stack (m : machine) (st : tree val_) : machine = { m with m_stack = st }
let set_rest (m : machine) (r : list instr) : machine = { m with m_rest = r }
let set_ctl (m : machine) (st : tree val_) (fp : nat) (c : code) (r : list instr) (ks : list cont) : machine =
  { m with m_stack = st; m_fp = fp; m_code = c; m_rest = r; m_conts = ks }
let set_handlers (m : machine) (hs : list handler) : machine = { m with m_handlers = hs }
let set_exn (m : machine) (e : val_) : machine = { m with m_exn = e }
let set_heap (m : machine) (h : tree obj) : machine = { m with m_heap = h }
let set_globals (m : machine) (gv gf : tree val_) (se : tree unit) (su : bool) : machine =
  { m with m_gval = gv; m_gfun = gf; m_sealed = se; m_seal_user = su }
let alloc (m : machine) (o : obj) : pos & machine =
  let l = m.m_next in
  (l, { m with m_heap = tset l o m.m_heap; m_next = l + 1; m_allocs = m.m_allocs + 1 })

let rec vlist (v : val_) : option (list val_) =
  match v with VNil -> Some [] | VPair a d -> option_map (Cons a) (vlist d) | _ -> None
let rec of_list (l : list val_) : val_ = match l with [] -> VNil | a :: d -> VPair a (of_list d)

let fix_min : int = -2305843009213693952
let fix_max : int = 2305843009213693951
let fix_fits (z : int) : bool = fix_min <= z && z <= fix_max
let is_number (v : val_) : bool = match v with VFix _ | VReal _ -> true | _ -> false
let number (v : val_) : nat = match v with VFix z -> of_Z z | VReal b -> b | _ -> 0

let compare_fix_real (i : int) (b : nat) : option comparison =
  match classify b with
  | CNan -> None
  | CInf neg -> Some (if neg then Gt else Lt)
  | _ -> (match ratio b with
    | Some (neg, n, den) -> Some (zcompare (i * den) (if neg then - n else n))
    | None -> None)

(* ---------- identity ---------- *)
let same (a b : val_) : option bool = match a, b with
  | VFix x, VFix y -> Some (x = y) | VSym x, VSym y -> Some (x = y)
  | VBool x, VBool y -> Some (x = y) | VNil, VNil -> Some true
  | VCleared, VCleared -> Some true | VPvar x, VPvar y -> Some (x = y)
  | VVec x, VVec y | VBytes x, VBytes y | VClo x, VClo y | VExn x, VExn y | VStream x, VStream y ->
    Some (x = y)
  | VPair _ _, VPair _ _ | VStr _, VStr _ | VReal _, VReal _ -> None
  | _, _ -> Some false

let rec text_eqb (a b : text) : bool = match a, b with
  | [], [] -> true | x :: a, y :: b -> x = y && text_eqb a b | _, _ -> false

(* ---------- = (sj_equal) ---------- *)
type eqr = | EqT | EqF | EqIdentity | EqCycle
let rec eq_list (f : val_ -> val_ -> eqr) (xs ys : list val_) : eqr = match xs, ys with
  | [], [] -> EqT
  | x :: xs, y :: ys -> (match f x y with EqT -> eq_list f xs ys | r -> r)
  | _, _ -> EqF

let rec eq_val (h : tree obj) (fuel : nat) (a b : val_) : Tot eqr (decreases %[fuel; a]) =
  if fuel = 0 then EqCycle else
  match a, b with
  | VPair a1 a2, VPair b1 b2 -> (match eq_val h fuel a1 b1 with EqT -> eq_val h fuel a2 b2 | r -> r)
  | VFix x, VFix y -> if x = y then EqT else EqF
  | VFix x, VReal y -> (match compare_fix_real x y with Some Eq -> EqT | _ -> EqF)
  | VReal x, VFix y -> (match compare_fix_real y x with Some Eq -> EqT | _ -> EqF)
  | VReal x, VReal y -> if is_nan x && is_nan y then EqIdentity else if eqv x y then EqT else EqF
  | VStr x, VStr y -> if text_eqb x y then EqT else EqF
  | VSym x, VSym y -> if x = y then EqT else EqF
  | VBool x, VBool y -> if x = y then EqT else EqF
  | VNil, VNil | VCleared, VCleared -> EqT
  | VPvar x, VPvar y -> if x = y then EqT else EqF
  | VClo x, VClo y | VExn x, VExn y | VStream x, VStream y -> if x = y then EqT else EqF
  | VVec x, VVec y ->
    if x = y then EqT else
    (match tget x h, tget y h with
     | Some (OVec xs), Some (OVec ys) -> eq_val_list h (fuel - 1) xs ys
     | _, _ -> EqCycle)
  | VBytes x, VBytes y ->
    if x = y then EqT else
    (match tget x h, tget y h with
     | Some (OBytes xs), Some (OBytes ys) -> if text_eqb xs ys then EqT else EqF
     | _, _ -> EqCycle)
  | _, _ -> EqF
and eq_val_list (h : tree obj) (fuel : nat) (xs ys : list val_) : Tot eqr (decreases %[fuel; xs]) =
  match xs, ys with
  | [], [] -> EqT
  | x :: xs', y :: ys' -> (match eq_val h fuel x y with EqT -> eq_val_list h fuel xs' ys' | r -> r)
  | _, _ -> EqF

let rec eq_val_list_is_eq_list (h : tree obj) (fuel : nat) (xs ys : list val_)
  : Lemma (eq_val_list h fuel xs ys == eq_list (eq_val h fuel) xs ys) =
  match xs, ys with
  | _ :: xs', _ :: ys' -> eq_val_list_is_eq_list h fuel xs' ys'
  | _ -> ()
let eq_fuel : nat = 4096

(* ---------- hash ---------- *)
let u64 (z : int) : int = zland z 18446744073709551615
let mix (x0 : int) : int =
  let x = zlxor x0 (zshiftr x0 33) in
  let x = u64 (x * 18397679294719823053) in
  let x = zlxor x (zshiftr x 33) in
  let x = u64 (x * 14181476777654086739) in
  zlxor x (zshiftr x 33)
let special_word (n : int) : int = n * 8 + 2

let rec hash_go (e : env) (h : tree obj) (fuel : nat) (v : val_) (budget0 : int)
  : Tot (int & int) (decreases fuel) =
  if fuel = 0 then (0, budget0) else
  let f : nat = fuel - 1 in
  let budget = budget0 - 1 in
  if budget < 0 then (0, budget) else
  match v with
  | VFix z -> (mix (u64 z), budget)
  | VReal b ->
    (match to_Z_exact b with
     | Some z -> if zabs z < 9200000000000000000 then (mix (u64 z), budget) else (mix b, budget)
     | None -> (mix b, budget))
  | VSym s -> (e.e_hash (text_of_sym s), budget)
  | VPair _ _ ->
    let rec walk (fl : nat) (x : val_) (acc budget : int) : Tot (int & int) (decreases fl) =
      if fl = 0 then (acc, budget) else
      match x with
      | VPair a d ->
        if budget <= 0 then (let (r, b) = hash_go e h f x budget in (mix (zlxor acc r), b))
        else (let (r, b) = hash_go e h f a budget in walk (fl - 1) d (mix (zlxor acc r)) b)
      | _ -> let (r, b) = hash_go e h f x budget in (mix (zlxor acc r), b) in
    walk 300 v 112 budget
  | VStr s -> (e.e_hash s, budget)
  | VBytes l -> (match tget l h with Some (OBytes bs) -> (e.e_hash bs, budget) | _ -> (0, budget))
  | VVec l -> (match tget l h with
    | Some (OVec cells) ->
      fold_left #(int & int) #val_ (fun st c -> let (acc, b) = st in
        if b <= 0 then st else let (r, b') = hash_go e h f c b in (mix (zlxor acc r), b'))
        cells (118, budget)
    | _ -> (0, budget))
  | VNil -> (mix (special_word 0), budget)
  | VBool false -> (mix (special_word 1), budget)
  | VBool true -> (mix (special_word 2), budget)
  | VCleared -> (mix (special_word 3), budget)
  | VPvar off -> (mix (off * 256 + 250), budget)
  | VClo _ -> (mix 80, budget)
  | VExn _ -> (mix 10, budget)
  | VStream _ -> (mix 9, budget)
let sj_hash (e : env) (h : tree obj) (v : val_) : int = fst (hash_go e h 300 v 256)

(* ---------- text of values ---------- *)
let fmt_real (b : nat) : text = format_real b
let to_string_atom (v : val_) : text = match v with
  | VFix z -> z_text z | VBool true -> t "true" | VBool false -> t "false" | VNil -> t "()"
  | VPvar o -> app (t "Var") (z_digits o) | VSym s -> text_of_sym s
  | VStr s -> app [34] (app s [34]) | VReal b -> fmt_real b
  | VPair _ _ -> t "#<pair>" | VClo _ -> t "#<procedure>" | VVec _ -> t "#<absvector>"
  | VStream _ -> t "#<stream>" | VBytes _ -> t "#<bytes>" | VExn _ -> t "#<exception>"
  | VCleared -> t "#<value>"

let sep_join (items : list text) : text =
  match items with [] -> [] | x :: r -> app x (flat_map #text #nat (fun (i : text) -> app #nat [32] i) r)
let is_fail (v : val_) : bool = match v with VSym s -> s = s_shen_fail_ | _ -> false
let show_vec (sh : val_ -> text) (cells : list val_) : text =
  let cut (l : text) : text = firstn 61 l in
  match cells with
  | VFix z :: rest ->
    if 0 <= z && z < length cells then
      app (t "<") (app (cut (sep_join (map (fun c -> if is_fail c then t "..." else cut (sh c))
                                          (firstn 61 (firstn (to_nat z) rest))))) (t ">"))
    else app (t "<<") (app (cut (sep_join (map (fun c -> cut (sh c)) (firstn 61 cells)))) (t ">>"))
  | _ -> app (t "<<") (app (cut (sep_join (map (fun c -> cut (sh c)) (firstn 61 cells)))) (t ">>"))

let rec show (h : tree obj) (fuel : nat) (v : val_) : Tot text (decreases fuel) =
  if fuel = 0 then [] else
  let f : nat = fuel - 1 in
  match v with
  | VPair a d ->
    let rec tail (fl : nat) (x : val_) : Tot text (decreases fl) =
      if fl = 0 then [] else
      match x with
      | VPair a d -> app (t " ") (app (show h f a) (tail (fl - 1) d))
      | VNil -> []
      | x -> app (t " | ") (show h f x) in
    app (t "[") (app (show h f a) (app (tail 64 d) (t "]")))
  | VVec l -> (match tget l h with
    | Some (OVec [VSym s; a; b]) ->
      if text_eqb (text_of_sym s) (t "shen.tuple")
      then app (t "(@p ") (app (show h f a) (app (t " ") (app (show h f b) (t ")"))))
      else show_vec (show h f) [VSym s; a; b]
    | Some (OVec cells) -> show_vec (show h f) cells
    | _ -> t "#<value>")
  | VStr s -> app [34] (app s [34])
  | VNil -> t "[]"
  | VClo _ -> t "#<procedure>" | VStream _ -> t "#<stream>" | VBytes _ -> t "#<bytes>"
  | VExn _ -> t "#<exception>" | VCleared -> t "#<value>"
  | x -> to_string_atom x

let show_cut (h : tree obj) (v : val_) : text =
  let s = show h 64 v in
  if length s <= 60 then s else app (firstn 60 s) (t "...")

let rec subst_tilde (m rep : text) : option text = match m with
  | 126 :: 83 :: r -> Some (app rep r)
  | c :: r -> option_map (Cons c) (subst_tilde r rep)
  | [] -> None
let exception_text (h : tree obj) (msg : text) (v : val_) : text = match v with
  | VCleared -> msg
  | _ -> let s = show_cut h v in
    (match subst_tilde msg s with Some r -> r | None -> app msg (app [32] s))

(* ---------- raising ---------- *)
let rec find_label (l : nat) (iss : list instr) : option (list instr) = match iss with
  | [] -> None
  | ILabel x :: r -> if x = l then Some r else find_label l r
  | _ :: r -> find_label l r

let raise (m : machine) (msg : text) (v : val_) : move =
  match m.m_handlers with
  | [] -> let (l, m') = alloc m (OExn msg v) in MFinal (FError (VExn l)) m'
  | h :: hs ->
    (match find_label h.h_label (code_ins h.h_code) with
     | None -> MStuck RBadLabel
     | Some r ->
       if h.h_quiet then
         MTau (set_exn (set_ctl (set_handlers m hs) m.m_stack h.h_fp h.h_code r h.h_conts) VNil)
       else
         let (l, m') = alloc m (OExn msg v) in
         MTau (set_exn (set_ctl (set_handlers m' hs) m'.m_stack h.h_fp h.h_code r h.h_conts) (VExn l)))
let raise_s (m : machine) (s : string) : move = raise m (t s) VCleared
let raise_v (m : machine) (s : string) (v : val_) : move = raise m (t s) v

let ret_to (m : machine) (d : nat) (v : val_) : move = MTau (set_stack m (swrite m d v))
let boolean (m : machine) (d : nat) (b : bool) = ret_to m d (VBool b)

(* ---------- installing code (loader.c) ---------- *)
type loaded (a : Type) = | LOk : x:a -> loaded a | LErr : msg:string -> loaded a
let small_int (v : val_) (limit : int) : option nat = match v with
  | VFix z -> if 0 <= z && z < limit then Some (to_nat z) else None
  | _ -> None
let lim (n : nat) : int = n
let operand_of (v : val_) (frame nconst : nat) : option operand = match v with
  | VPair (VSym c) (VPair k VNil) ->
    if c = s_const then option_map OConst (small_int k (lim nconst)) else None
  | VPair _ _ -> None
  | _ -> option_map OSlot (small_int v (lim frame))
let rec all_some (#a : Type) (l : list (option a)) : option (list a) = match l with
  | [] -> Some []
  | None :: _ -> None
  | Some x :: r -> option_map (Cons x) (all_some r)
let rec prim_lookup (s : pos) (l : list (string & prim & nat)) : option (prim & nat) = match l with
  | [] -> None
  | (n, p, a) :: r -> if sym n = s then Some (p, a) else prim_lookup s r

let b2 : int = 4294967295
let sn (v : val_) (f : nat) = small_int v (lim f)
let window_ok (a count frame : nat) : bool = a + 1 + count < frame

let encode (ptab : tree (prim & nat)) (insn : val_) (frame nconst ncode : nat) : loaded instr =
  match vlist insn with
  | None | Some [] -> LErr "malformed instruction"
  | Some (VSym op :: args) ->
    let bad = LErr "bad operand" in
    let cnt = LErr "wrong operand count" in
    let win = LErr "call window outside the frame" in
    let iss (s : string) : bool = op = sym s in
    if iss "move" then (match args with
      | [d; s] -> (match sn d frame, sn s frame with Some d, Some s -> LOk (IMove d s) | _, _ -> bad)
      | _ -> cnt)
    else if iss "const" then (match args with
      | [d; k] -> (match sn d frame, sn k nconst with Some d, Some k -> LOk (IConst d k) | _, _ -> bad)
      | _ -> cnt)
    else if iss "capture" then (match args with
      | [d; i] -> (match sn d frame, small_int i 256 with Some d, Some i -> LOk (ICapture d i) | _, _ -> bad)
      | _ -> cnt)
    else if iss "closure" then (match args with
      | d :: c :: ss -> (match sn d frame, sn c ncode, all_some (map (fun s -> sn s frame) ss) with
        | Some d, Some c, Some ss -> LOk (IClosure d c ss) | _, _, _ -> bad)
      | _ -> cnt)
    else if iss "prim" then (match args with
      | d :: VSym p :: os ->
        (match sn d frame with None -> bad | Some d ->
         match tget p ptab with
         | Some (pr, a) ->
           if a = length os then
             (match all_some (map (fun o -> operand_of o frame nconst) os) with
              | Some os -> LOk (IPrim d pr os) | None -> bad)
           else LErr "unknown primitive or wrong arity"
         | None -> LErr "unknown primitive or wrong arity")
      | _ :: _ :: _ -> LErr "unknown primitive or wrong arity"
      | _ -> cnt)
    else if iss "label" then (match args with
      | [l] -> (match small_int l b2 with Some l -> LOk (ILabel l) | None -> bad) | _ -> cnt)
    else if iss "jump" then (match args with
      | [l] -> (match small_int l b2 with Some l -> LOk (IJump l) | None -> bad) | _ -> cnt)
    else if iss "jump-if-false" then (match args with
      | [o; l] -> (match operand_of o frame nconst, small_int l b2 with
        | Some o, Some l -> LOk (IJumpIfFalse o l) | _, _ -> bad)
      | _ -> cnt)
    else if iss "call" || iss "call-sealed" then (match args with
      | [d; a; VSym f; n] -> (match sn d frame, sn a frame, small_int n 256 with
        | Some d, Some a, Some n ->
          if window_ok a n frame then LOk (if iss "call" then ICall d a f n else ICallSealed d a f n) else win
        | _, _, _ -> bad)
      | [_; _; _; _] -> bad
      | _ -> cnt)
    else if iss "call-value" then (match args with
      | [d; a; n] -> (match sn d frame, sn a frame, small_int n 256 with
        | Some d, Some a, Some n -> if window_ok a n frame then LOk (ICallValue d a n) else win
        | _, _, _ -> bad)
      | _ -> cnt)
    else if iss "tail-call" || iss "tail-call-sealed" then (match args with
      | [a; VSym f; n] -> (match sn a frame, small_int n 256 with
        | Some a, Some n ->
          if window_ok a n frame then LOk (if iss "tail-call" then ITail a f n else ITailSealed a f n) else win
        | _, _ -> bad)
      | [_; _; _] -> bad
      | _ -> cnt)
    else if iss "tail-call-value" then (match args with
      | [a; n] -> (match sn a frame, small_int n 256 with
        | Some a, Some n -> if window_ok a n frame then LOk (ITailValue a n) else win
        | _, _ -> bad)
      | _ -> cnt)
    else if iss "return" then (match args with
      | [o] -> (match operand_of o frame nconst with Some o -> LOk (IReturn o) | None -> bad) | _ -> cnt)
    else if iss "push-handler" then (match args with
      | [l] -> (match small_int l b2 with Some l -> LOk (IPushHandler l) | None -> bad) | _ -> cnt)
    else if iss "pop-handler" then (match args with [] -> LOk IPopHandler | _ -> cnt)
    else if iss "exception" then (match args with
      | [d] -> (match sn d frame with Some d -> LOk (IException d) | None -> bad) | _ -> cnt)
    else if iss "entry" then (match args with
      | [n; l] -> (match small_int n 256, small_int l b2 with
        | Some n, Some l -> LOk (IEntry n l) | _, _ -> bad)
      | _ -> cnt)
    else if iss "jump-unless-entry" then (match args with
      | [s; n; l] -> (match sn s frame, small_int n 256, small_int l b2 with
        | Some s, Some n, Some l -> LOk (IJumpUnlessEntry s n l) | _, _, _ -> bad)
      | _ -> cnt)
    else if iss "inline" then (match args with
      | [VSym f; n] -> (match small_int n b2 with Some n -> LOk (IInline f n) | None -> bad)
      | [_; _] -> bad
      | _ -> cnt)
    else LErr "unknown instruction"
  | Some _ -> LErr "unknown instruction"

let excluded_ops : list string =
 ["loop";"again";"real-number";"real-box";"real-move";"real-neg";"real-abs";"real-sqrt";"real+";"real-";"real*";"real/"
 ;"real-unless<";"real-unless>";"real-unless<=";"real-unless>=";"real-unless=";"real-load";"real-store"
 ;"real-load-at";"real-store-at";"real-from-word";"word-from-real";"word-number";"word-box";"word-move"
 ;"word+";"word-";"word*";"word-and";"word-or";"word-xor";"word-shl";"word-shr";"word-sar";"word-rotl";"word-rotr"
 ;"word-unless<";"word-unless>";"word-unless<=";"word-unless>=";"word-unless=";"word-unless-u<";"word-unless-u>"
 ;"word-unless-u<=";"word-unless-u>=";"word-load8";"word-load16";"word-load32";"word-load-s32";"word-load64"
 ;"word-store8";"word-store16";"word-store32";"word-store64"]

let target_of (i : instr) : option nat = match i with
  | IJump l | IPushHandler l | IJumpIfFalse _ l | IEntry _ l | IJumpUnlessEntry _ _ l -> Some l
  | _ -> None
let rec labels_of (iss : list instr) : list nat = match iss with
  | [] -> [] | ILabel l :: r -> l :: labels_of r | _ :: r -> labels_of r
let rec nodup_N (l : list nat) : bool = match l with
  | [] -> true | x :: r -> not (existsb (fun y -> x = y) r) && nodup_N r
let is_entry (i : instr) = match i with IEntry _ _ -> true | _ -> false
let is_transfer (i : instr) = match i with
  | IReturn _ | IJump _ | ITail _ _ _ | ITailSealed _ _ _ | ITailValue _ _ -> true | _ -> false
let check_control (iss : list instr) : bool =
  match iss with [] -> false | first :: rest ->
    let ls = labels_of iss in
    nodup_N ls
    && forallb (fun i -> match target_of i with
                 | Some l -> existsb (fun y -> l = y) ls | None -> true) iss
    && not (existsb is_entry rest)
    && is_transfer (last iss first)

let rec map_loaded (#a #b : Type) (f : a -> loaded b) (l : list a) : loaded (list b) = match l with
  | [] -> LOk []
  | x :: r -> (match f x with
    | LErr e -> LErr e
    | LOk y -> (match map_loaded f r with LErr e -> LErr e | LOk ys -> LOk (y :: ys)))

let rec build_code (ptab : tree (prim & nat)) (fuel : nat) (form : val_) : Tot (loaded code) (decreases fuel) =
  if fuel = 0 then LErr "malformed code object" else
  let f : nat = fuel - 1 in
  match vlist form with
  | Some (VSym hd :: name :: arity :: frame :: consts :: insns :: codes :: more) ->
    if not (hd = s_code) then LErr "malformed code object" else
    let more_ok = (match more with [] | [_] -> true | _ -> false) in
    (match more_ok, small_int arity 256, small_int frame 1048576, vlist consts, vlist insns, vlist codes with
     | true, Some ar, Some fr, Some cs, Some iss, Some ns ->
       if fr < ar + 2 then LErr "malformed code object" else
       let inl = (match more with [x] -> x | _ -> VNil) in
       (match map_loaded (build_code ptab f) ns with
        | LErr e -> LErr e
        | LOk nested ->
          (match map_loaded (fun i -> encode ptab i fr (length cs) (length ns)) iss with
           | LErr e -> LErr e
           | LOk ins ->
             if not (check_control ins) then LErr "bad control flow: labels or the final instruction" else
             (match ins with
              | IEntry n l :: _ ->
                if n <= ar || fr < n + 2
                then LErr "entry outside the frame or not above the arity"
                else LOk (Code name ar (Some (n, l)) fr cs ins nested inl)
              | _ -> LOk (Code name ar None fr cs ins nested inl))))
     | _, _, _, _, _, _ -> LErr "malformed code object")
  | _ -> LErr "malformed code object"

let prim_tree : tree (prim & nat) =
  fold_left #(tree (prim & nat)) #(string & prim & nat)
    (fun tr e -> let (n, p, a) = e in tset (sym n) (p, a) tr) prim_table Leaf

let install (ptab : tree (prim & nat)) (m : machine) (d : nat) (form : val_) : move =
  let build (c : val_) : either string (pos & machine) =
    match build_code ptab 64 c with
    | LErr e -> Inl e
    | LOk code -> Inr (alloc m (OClo code [])) in
  match vlist form with
  | Some [VSym h; VSym name; c] ->
    if h = s_defun then
      (match tget name m.m_sealed with
       | Some _ -> raise_v m "~S is sealed and cannot be redefined" (VSym name)
       | None ->
         (match build c with
          | Inl e -> raise_s m e
          | Inr (l, m') ->
            let se = if m'.m_seal_user then tset name () m'.m_sealed else m'.m_sealed in
            let m'' = set_globals m' m'.m_gval (tset name (VClo l) m'.m_gfun) se m'.m_seal_user in
            ret_to m'' d (VSym name)))
    else raise_s m "install: expected (defun Name Code) or a code object"
  | _ ->
    (match form with
     | VPair (VSym h) _ ->
       if h = s_code then
         (match build form with
          | Inl e -> raise_s m e
          | Inr (l, m') -> ret_to m' d (VClo l))
       else raise_s m "install: expected (defun Name Code) or a code object"
     | _ -> raise_s m "install: expected (defun Name Code) or a code object")

(* ---------- primitives ---------- *)
let symbol_char (c : nat) : bool =
  (97 <= c && c <= 122) || (65 <= c && c <= 90) || (48 <= c && c <= 57)
  || existsb (fun y -> c = y) (t "=-*/+_?$!@~.><&%'#`")
let name_kind (s : text) : int = match s with
  | [c] -> if existsb (fun y -> c = y) (t "{}:;,") then 1
           else if 48 <= c && c <= 57 then 0
           else if symbol_char c then (if 65 <= c && c <= 90 then 2 else 1) else 0
  | [] -> 0
  | c :: _ ->
    if 48 <= c && c <= 57 then 0
    else if forallb symbol_char s then (if 65 <= c && c <= 90 then 2 else 1) else 0

let rec replace (#a : Type) (n : nat) (x : a) (l : list a) : list a = match l with
  | [] -> []
  | y :: r -> if n = 0 then x :: r else y :: replace (n - 1) x r

let rec le_read (bs : list nat) : nat = match bs with [] -> 0 | b :: r -> b + 256 * le_read r
let rec le_bytes (w : nat) (x : nat) : list nat =
  if w = 0 then [] else nland x 255 :: le_bytes (w - 1) (nshiftr x 8)
let splice (#a : Type) (at_ : nat) (src dst : list a) : list a =
  app (firstn at_ dst) (app src (skipn (at_ + length src) dst))

let word_of (z : int) : int = u64 (z * 4)
let of_word (w : int) : int =
  let s = if ztestbit w 63 then w - 18446744073709551616 else w in zdiv s 4
let rec popc (fuel : nat) (w : int) : int =
  if fuel = 0 then 0 else if w = 0 then 0 else zland w 1 + popc (fuel - 1) (zshiftr w 1)
let clz64 (w : int) : int = 63 - zlog2 w
let rec ctz_go (fuel : nat) (w : int) (n : int) : int =
  if fuel = 0 then n else if ztestbit w 0 then n else ctz_go (fuel - 1) (zshiftr w 1) (n + 1)

let vec_cells (m : machine) (l : pos) : list val_ =
  match tget l m.m_heap with Some (OVec c) -> c | _ -> []
let put_vec (m : machine) (l : pos) (c : list val_) : machine = set_heap m (tset l (OVec c) m.m_heap)

(* ---------- dictionaries ---------- *)
let dict_parts (m : machine) (d : val_) : option (pos & val_ & int & pos & list val_) =
  match d with
  | VVec l -> (match vec_cells m l with
    | [tag; VFix n; VVec b] ->
      if n < 0 then None else
      let bs = vec_cells m b in
      let len : nat = length bs in
      if 0 < len && nland len (nsub len 1) = 0
      then Some (l, tag, n, b, bs) else None
    | _ -> None)
  | _ -> None
let bucket_index (e : env) (m : machine) (k : val_) (len : nat) : nat =
  to_nat (zland (sj_hash e m.m_heap k) (len - 1))
let rec bucket_find (h : tree obj) (k : val_) (c : val_) : option (option (val_ & val_)) = match c with
  | VNil -> Some None
  | VPair (VPair kk vv) r ->
    (match eq_val h eq_fuel kk k with
     | EqT -> Some (Some (kk, vv))
     | EqF -> bucket_find h k r
     | _ -> None)
  | _ -> None

let bytes_of (m : machine) (l : pos) : list nat =
  match tget l m.m_heap with Some (OBytes b) -> b | _ -> []
let put_bytes (m : machine) (l : pos) (b : list nat) : machine = set_heap m (tset l (OBytes b) m.m_heap)

let allocates (p : prim) : bool = match p with
  | PAdd | PSub | PMul | PDiv | PCons | PCn | PTlstr | PStr | PAbsvector | PFilledVector | PAbsvector3
  | PAppend | PBytesNew | PStringBytes | PBytesString | PDictPut | PDictEntries | PDecimal | PPos | PNString
  | PGetTime | POpen | PReadFile -> true
  | _ -> false

let is_excluded (p : prim) : bool = match p with
  | PMarkToplevel | PTraceText | PBacktrace | PSaveExecutable | PThread | PForeign
  | PPointerKind | PPointerAddress | PBytesPointer | PPointerString | PPointerBytes | PErrno | PCErrno
  | PPointerKill
  | PS32 | PS64 | PF32 | PF64 | PSetS32 | PSetS64 | PSetF32 | PSetF64
  | PPointerSized | PSetPointer | PPointerGuard | PPointerOwner | PPointersDead | PPointerReadOnly -> true
  | _ -> false

(* The catch-all branch of Rocq's prim_step. *)
let prim_fallback (q : prim) : move = if is_excluded q then MStuck (RExcluded q) else MStuck RArgs

let rec put_in (h : tree obj) (k v : val_) (c : val_) : val_ = match c with
  | VPair (VPair kk vv) r ->
    (match eq_val h eq_fuel kk k with
     | EqT -> VPair (VPair kk v) r | _ -> VPair (VPair kk vv) (put_in h k v r))
  | x -> x
let rec dict_rm (h : tree obj) (k : val_) (c : val_) : val_ = match c with
  | VPair (VPair kk vv) r ->
    (match eq_val h eq_fuel kk k with
     | EqT -> r | _ -> VPair (VPair kk vv) (dict_rm h k r))
  | x -> x
let rec regroup (e : env) (m : machine) (len : nat) (cl : val_) (acc : list val_) : list val_ = match cl with
  | VPair (VPair kk vv) r ->
    let j = bucket_index e m kk len in
    let cur = (match nth_error acc j with Some x -> x | None -> VNil) in
    regroup e m len r (replace j (VPair (VPair kk vv) cur) acc)
  | _ -> acc
let rec dict_walk (c : val_) (acc : val_) : val_ = match c with
  | VPair (VPair kk vv) r -> dict_walk r (VPair (VPair kk vv) acc) | _ -> acc
let rec split_exp (l acc : text) : text & int = match l with
  | 101 :: r ->
    let (neg, ds) = (match r with 45 :: q -> (true, q) | 43 :: q -> (false, q) | _ -> (false, r)) in
    let (v, _, _) = scan_digits ds 0 0 in (rev acc, (if neg then - v else v))
  | c :: r -> split_exp r (c :: acc)
  | [] -> (rev acc, 0)

let rec deref_go (m : machine) (d : nat) (b mark : val_) (fuel : nat) (x : val_) : Tot move (decreases fuel) =
  if fuel = 0 then MStuck RCyclic else
  match x with
  | VPvar off -> (match b with
    | VVec l -> (match nth_error (vec_cells m l) (to_nat off) with
      | Some bnd -> (match same bnd mark with
        | Some true -> ret_to m d x
        | Some false -> deref_go m d b mark (fuel - 1) bnd
        | None -> MStuck RIdentity)
      | None -> raise_v m "shen-jit.deref: ~S has no binding here" x)
    | _ -> raise_v m "shen-jit.deref: ~S has no binding here" x)
  | _ -> ret_to m d x

let prim_step (e : env) (ptab : tree (prim & nat)) (m : machine) (d : nat) (p : prim) (args : list val_) : move =
  let ret = ret_to m d in
  let isb = boolean m d in
  match p with
  | PAdd | PSub | PMul | PDiv -> (match args with
    | [a; b] ->
      if not (is_number a) then raise_v m "~S is not a number" a
      else if not (is_number b) then raise_v m "~S is not a number" b
      else if (match p, b with
               | PDiv, VFix z -> z = 0 | PDiv, VReal r -> is_zero r | _, _ -> false)
      then raise_s m "division by zero"
      else (match a, b with
       | VFix x, VFix y ->
         (match p with
          | PDiv ->
            if not (zrem x y = 0) then ret (VReal (div (of_Z x) (of_Z y)))
            else let r = zquot x y in if fix_fits r then ret (VFix r) else raise_s m "integer overflow"
          | _ ->
            let r = (match p with PAdd -> x + y | PSub -> x - y | _ -> x * y) in
            if fix_fits r then ret (VFix r) else raise_s m "integer overflow")
       | _, _ ->
         let x = number a in let y = number b in
         ret (VReal (match p with PAdd -> add x y | PSub -> sub x y | PMul -> mul x y | _ -> div x y)))
    | _ -> prim_fallback p)
  | PLt | PGt | PLe | PGe -> (match args with
    | [a; b] ->
      if not (is_number a) then raise_v m "~S is not a number" a
      else if not (is_number b) then raise_v m "~S is not a number" b
      else (match a, b with
       | VFix x, VFix y -> isb (match p with
           | PLt -> x < y | PGt -> x > y | PLe -> x <= y | _ -> x >= y)
       | VFix x, VReal r -> isb (match compare_fix_real x r, p with
           | Some Lt, PLt | Some Lt, PLe | Some Gt, PGt | Some Gt, PGe | Some Eq, PLe | Some Eq, PGe -> true
           | _, _ -> false)
       | VReal r, VFix y -> isb (match compare_fix_real y r, p with
           | Some Gt, PLt | Some Gt, PLe | Some Lt, PGt | Some Lt, PGe | Some Eq, PLe | Some Eq, PGe -> true
           | _, _ -> false)
       | _, _ ->
         let x = number a in let y = number b in
         isb (match p with PLt -> lt x y | PGt -> gt x y | PLe -> le x y | _ -> ge x y))
    | _ -> prim_fallback p)
  | PEq -> (match args with
    | [a; b] -> (match eq_val m.m_heap eq_fuel a b with
      | EqT -> isb true | EqF -> isb false
      | EqIdentity -> MStuck RIdentity | EqCycle -> MStuck RCyclic)
    | _ -> prim_fallback p)
  | PNumberp -> (match args with [a] -> isb (is_number a) | _ -> prim_fallback p)
  | PCollect -> (match args with [] -> isb true | _ -> prim_fallback p)
  | PCons -> (match args with [a; b] -> ret (VPair a b) | _ -> prim_fallback p)
  | PHd -> (match args with
    | [v] -> (match v with VPair a _ -> ret a | _ -> raise_v m "hd: ~S is not a pair" v)
    | _ -> prim_fallback p)
  | PTl -> (match args with
    | [v] -> (match v with VPair _ b -> ret b | _ -> raise_v m "tl: ~S is not a pair" v)
    | _ -> prim_fallback p)
  | PConsp -> (match args with [v] -> isb (match v with VPair _ _ -> true | _ -> false) | _ -> prim_fallback p)
  | PStringp -> (match args with [v] -> isb (match v with VStr _ -> true | _ -> false) | _ -> prim_fallback p)
  | PAbsvector -> (match args with
    | [v] -> (match v with
      | VFix n -> if n < 0 || 281474976710656 <= n then raise_v m "absvector: ~S is not a valid length" v else
        let (l, m') = alloc m (OVec (repeat (VSym s_shen_fail_) (to_nat n))) in ret_to m' d (VVec l)
      | _ -> raise_v m "absvector: ~S is not a valid length" v)
    | _ -> prim_fallback p)
  | PAbsvectorp -> (match args with [v] -> isb (match v with VVec _ -> true | _ -> false) | _ -> prim_fallback p)
  | PGetAddress -> (match args with
    | [v; i] -> (match v with
      | VVec l -> (match i with
        | VFix z -> if z < 0 then raise_v m "<-address: ~S is not a valid index" i else
          (match nth_error (vec_cells m l) (to_nat z) with
           | Some x -> ret x | None -> raise_v m "<-address: ~S is not a valid index" i)
        | _ -> raise_v m "<-address: ~S is not a valid index" i)
      | _ -> raise_v m "<-address: ~S is not an absvector" v)
    | _ -> prim_fallback p)
  | PSetAddress -> (match args with
    | [v; i; x] -> (match v with
      | VVec l -> (match i with
        | VFix z ->
          if z < 0 || length (vec_cells m l) <= to_nat z
          then raise_v m "address->: ~S is not a valid index" i
          else ret_to (put_vec m l (replace (to_nat z) x (vec_cells m l))) d v
        | _ -> raise_v m "address->: ~S is not a valid index" i)
      | _ -> raise_v m "address->: ~S is not an absvector" v)
    | _ -> prim_fallback p)
  | PSet -> (match args with
    | [a; b] -> (match a with
      | VSym s -> ret_to (set_globals m (tset s b m.m_gval) m.m_gfun m.m_sealed m.m_seal_user) d b
      | _ -> raise_v m "set: ~S is not a symbol" a)
    | _ -> prim_fallback p)
  | PValue -> (match args with
    | [a] -> (match a with
      | VSym s -> (match tget s m.m_gval with
        | Some VCleared | None -> raise_v m "~S has no value" a
        | Some v -> ret v)
      | _ -> raise_v m "value: ~S is not a symbol" a)
    | _ -> prim_fallback p)
  | PSimpleError -> (match args with
    | [a] -> (match a with
      | VStr s -> raise m s VCleared
      | _ -> raise_v m "simple-error: ~S is not a string" a)
    | _ -> prim_fallback p)
  | PErrorToString -> (match args with
    | [a] -> (match a with
      | VExn l -> (match tget l m.m_heap with
        | Some (OExn msg v) -> ret (VStr (exception_text m.m_heap msg v))
        | _ -> MStuck RBadCode)
      | _ -> raise_v m "error-to-string: ~S is not an exception" a)
    | _ -> prim_fallback p)
  | PCn -> (match args with
    | [a; b] -> (match a, b with
      | VStr x, VStr y -> ret (VStr (app x y))
      | VStr _, _ -> raise_v m "cn: ~S is not a string" b
      | _, _ -> raise_v m "cn: ~S is not a string" a)
    | _ -> prim_fallback p)
  | PPos -> (match args with
    | [a; b] -> (match a with
      | VStr s -> (match b with
        | VFix z -> if z < 0 then raise_v m "pos: ~S is not a valid index" b else
          (match nth_error s (to_nat z) with
           | Some c -> ret (VStr [c]) | None -> raise_v m "pos: ~S is not a valid index" b)
        | _ -> raise_v m "pos: ~S is not a valid index" b)
      | _ -> raise_v m "pos: ~S is not a string" a)
    | _ -> prim_fallback p)
  | PTlstr -> (match args with
    | [a] -> (match a with
      | VStr (_ :: r) -> ret (VStr r)
      | _ -> raise_v m "tlstr: ~S is not a non-empty string" a)
    | _ -> prim_fallback p)
  | PStr -> (match args with [a] -> ret (VStr (to_string_atom a)) | _ -> prim_fallback p)
  | PNString -> (match args with
    | [a] -> (match a with
      | VFix z -> if 0 <= z && z <= 255 then ret (VStr [to_nat z])
                  else raise_v m "n->string: ~S is not a byte" a
      | _ -> raise_v m "n->string: ~S is not a byte" a)
    | _ -> prim_fallback p)
  | PStringN -> (match args with
    | [a] -> (match a with
      | VStr (c :: _) -> ret (VFix c)
      | _ -> raise_v m "string->n: ~S is not a non-empty string" a)
    | _ -> prim_fallback p)
  | PIntern -> (match args with
    | [a] -> (match a with
      | VStr s -> if text_eqb s (t "true") then ret (VBool true)
                  else if text_eqb s (t "false") then ret (VBool false)
                  else ret (VSym (sym_of_text s))
      | _ -> raise_v m "intern: ~S is not a string" a)
    | _ -> prim_fallback p)
  | PEvalKl -> (match args with [_] -> raise_s m "eval-kl is lowered as a call to shen-jit.eval-kl" | _ -> prim_fallback p)
  | PCharStreamp -> (match args with [_] -> isb false | _ -> prim_fallback p)
  | PReadUnitString -> (match args with [_] -> raise_s m "character streams are not supported" | _ -> prim_fallback p)
  | PWriteString -> (match args with [_; _] -> raise_s m "character streams are not supported" | _ -> prim_fallback p)
  | PInstall -> (match args with [form] -> install ptab m d form | _ -> prim_fallback p)
  | PSymbolp -> (match args with [a] -> isb (match a with VSym _ -> true | _ -> false) | _ -> prim_fallback p)
  | PHash -> (match args with
    | [a; b] -> (match b with
      | VFix n -> if n <= 0 then raise_v m "hash: ~S is not a valid bound" b else
        let h = zrem (sj_hash e m.m_heap a) n in ret (VFix (if h = 0 then 1 else h))
      | _ -> raise_v m "hash: ~S is not a valid bound" b)
    | _ -> prim_fallback p)
  | PExit -> (match args with
    | [a] -> (match a with
      | VFix z -> if 0 <= z && z <= 255 then MFinal (FExit z) m
                  else raise_v m "~S is not an exit status" a
      | _ -> raise_v m "~S is not an exit status" a)
    | _ -> prim_fallback p)
  | PSymbolKind -> (match args with
    | [a] -> ret (VFix (match a with VSym s -> name_kind (text_of_sym s) | _ -> 0))
    | _ -> prim_fallback p)
  | PFilledVector -> (match args with
    | [a; x] -> (match a with
      | VFix n -> if n < 0 || 281474976710656 <= n then raise_v m "shen-jit.filled-vector: ~S is not a valid length" a else
        let (l, m') = alloc m (OVec (repeat x (to_nat n))) in ret_to m' d (VVec l)
      | _ -> raise_v m "shen-jit.filled-vector: ~S is not a valid length" a)
    | _ -> prim_fallback p)
  | PDictFind -> (match args with
    | [dv; k] -> (match dict_parts m dv with
      | None -> raise_v m "~S is not a dictionary" dv
      | Some (_, _, _, _, bs) ->
        (match nth_error bs (bucket_index e m k (length bs)) with
         | Some c -> (match bucket_find m.m_heap k c with
           | Some (Some (kk, vv)) -> ret (VPair kk vv)
           | Some None -> ret VNil
           | None -> raise_v m "~S is not a dictionary" dv)
         | None -> raise_v m "~S is not a dictionary" dv))
    | _ -> prim_fallback p)
  | PDictPut -> (match args with
    | [dv; k; v] -> (match dict_parts m dv with
      | None -> raise_v m "~S is not a dictionary" dv
      | Some (l, tag, n, b, bs) ->
        let i = bucket_index e m k (length bs) in
        let c = (match nth_error bs i with Some c -> c | None -> VNil) in
        (match bucket_find m.m_heap k c with
         | None -> raise_v m "~S is not a dictionary" dv
         | Some (Some _) -> ret_to (put_vec m b (replace i (put_in m.m_heap k v c) bs)) d v
         | Some None ->
           let bs' = replace i (VPair (VPair k v) c) bs in
           let m1 = put_vec m b bs' in
           let n' = n + 1 in
           if length bs < n' then
             let len : nat = 2 * length bs in
             let fresh = fold_left #(list val_) #val_ (fun acc cell_list -> regroup e m len cell_list acc)
                           (vec_cells m1 b) (repeat VNil len) in
             let (nb, m2) = alloc m1 (OVec fresh) in
             ret_to (put_vec m2 l [tag; VFix n'; VVec nb]) d v
           else ret_to (put_vec m1 l [tag; VFix n'; VVec b]) d v))
    | _ -> prim_fallback p)
  | PDictRemove -> (match args with
    | [dv; k] -> (match dict_parts m dv with
      | None -> raise_v m "~S is not a dictionary" dv
      | Some (l, tag, n, b, bs) ->
        let i = bucket_index e m k (length bs) in
        let c = (match nth_error bs i with Some c -> c | None -> VNil) in
        (match bucket_find m.m_heap k c with
         | None -> raise_v m "~S is not a dictionary" dv
         | Some None -> ret k
         | Some (Some _) -> ret_to (put_vec (put_vec m b (replace i (dict_rm m.m_heap k c) bs)) l [tag; VFix (n - 1); VVec b]) d k))
    | _ -> prim_fallback p)
  | PDictEntries -> (match args with
    | [dv] -> (match dict_parts m dv with
      | None -> raise_v m "~S is not a dictionary" dv
      | Some (_, _, _, _, bs) ->
        ret (fold_left #val_ #val_ (fun acc c -> dict_walk c acc) bs VNil))
    | _ -> prim_fallback p)
  | PTaggedp -> (match args with
    | [a; b] -> (match a with
      | VVec l -> (match vec_cells m l with
        | x :: _ -> (match same x b with Some r -> isb r | None -> MStuck RIdentity)
        | [] -> isb false)
      | _ -> isb false)
    | _ -> prim_fallback p)
  | PSealedp -> (match args with
    | [a] -> (match a with
      | VSym s -> isb (match tget s m.m_sealed with
        | Some _ -> true
        | None -> m.m_seal_user && (match tget s m.m_gfun with Some (VClo _) -> false | _ -> true))
      | _ -> isb false)
    | _ -> prim_fallback p)
  | PSealing -> (match args with
    | [a] -> (match a with
      | VBool b -> ret_to (set_globals m m.m_gval m.m_gfun m.m_sealed b) d a
      | _ -> raise_v m "~S is not a boolean" a)
    | _ -> prim_fallback p)
  | PInlineBody -> (match args with
    | [a] -> (match a with
      | VSym s -> (match tget s m.m_gfun with
        | Some (VClo l) -> (match tget l m.m_heap with
          | Some (OClo c _) -> ret (code_inline c) | _ -> ret VNil)
        | _ -> ret VNil)
      | _ -> ret VNil)
    | _ -> prim_fallback p)
  | PVectorp -> (match args with
    | [a] -> (match a with
      | VVec l -> (match vec_cells m l with
        | VFix z :: _ -> isb (0 <= z)
        | VReal r :: _ -> isb (ge r 0)
        | _ -> isb false)
      | _ -> isb false)
    | _ -> prim_fallback p)
  | PAbsvector3 -> (match args with
    | [a; b; c] -> let (l, m') = alloc m (OVec [a; b; c]) in ret_to m' d (VVec l)
    | _ -> prim_fallback p)
  | PQuietp -> (match args with
    | [] -> isb (match m.m_handlers with h :: _ -> h.h_quiet | [] -> false)
    | _ -> prim_fallback p)
  | PIntegerp -> (match args with
    | [a] -> isb (match a with
      | VFix _ -> true
      | VReal r -> (match to_Z_exact r with Some _ -> true | None -> false)
      | _ -> false)
    | _ -> prim_fallback p)
  | PAppend -> (match args with
    | [a; b] -> (match vlist a with
      | Some l -> ret (fold_right VPair b l)
      | None -> raise_s m "attempt to append a non-list")
    | _ -> prim_fallback p)
  | PArityp -> (match args with
    | [a; b] -> (match a, b with
      | VSym s, VFix n -> (match tget s m.m_gfun with
        | Some (VClo l) -> (match tget l m.m_heap with
          | Some (OClo c _) -> isb (code_arity c = n) | _ -> isb false)
        | _ -> isb false)
      | _, _ -> isb false)
    | _ -> prim_fallback p)
  | PInlinedp -> (match args with
    | [a; b] -> (match a with
      | VSym s -> (match tget s m.m_gfun with
        | Some (VClo l) -> (match tget l m.m_heap with
          | Some (OClo c _) ->
            (match eq_val m.m_heap eq_fuel (code_inline c) b with
             | EqT -> isb true | EqF -> isb false | EqIdentity -> MStuck RIdentity | EqCycle -> MStuck RCyclic)
          | _ -> isb false)
        | _ -> isb false)
      | _ -> isb false)
    | _ -> prim_fallback p)
  | PBytesNew -> (match args with
    | [a] -> (match a with
      | VFix n -> if n < 0 || 281474976710656 <= n then raise_v m "shen-jit.bytes: ~S is not a valid length" a else
        let (l, m') = alloc m (OBytes (repeat 0 (to_nat n))) in ret_to m' d (VBytes l)
      | _ -> raise_v m "shen-jit.bytes: ~S is not a valid length" a)
    | _ -> prim_fallback p)
  | PBytesp -> (match args with [a] -> isb (match a with VBytes _ -> true | _ -> false) | _ -> prim_fallback p)
  | PBytesLength -> (match args with
    | [a] -> (match a with
      | VBytes l -> ret (VFix (length (bytes_of m l)))
      | _ -> raise_v m "bytes: ~S is not a byte buffer" a)
    | _ -> prim_fallback p)
  | PU8 | PU16 | PU32 -> (match args with
    | [b; i] ->
      let w : nat = (match p with PU8 -> 1 | PU16 -> 2 | _ -> 4) in
      (match b with
       | VBytes l -> (match i with
         | VFix z ->
           if z < 0 || length (bytes_of m l) < z + w
           then raise_v m "bytes: ~S is not a valid index" i
           else ret (VFix (le_read (firstn w (skipn (to_nat z) (bytes_of m l)))))
         | _ -> raise_v m "bytes: ~S is not a valid index" i)
       | _ -> raise_v m "bytes: ~S is not a byte buffer" b)
    | _ -> prim_fallback p)
  | PSetU8 | PSetU16 | PSetU32 -> (match args with
    | [b; i; x] ->
      let w : nat = (match p with PSetU8 -> 1 | PSetU16 -> 2 | _ -> 4) in
      (match b with
       | VBytes l -> (match i with
         | VFix z ->
           if z < 0 || length (bytes_of m l) < z + w
           then raise_v m "bytes: ~S is not a valid index" i
           else (match x with
             | VFix y ->
               if y < 0 || zshiftl 1 (8 * w) <= y then raise_v m "bytes: ~S does not fit" x
               else ret_to (put_bytes m l (splice (to_nat z) (le_bytes w (to_nat y)) (bytes_of m l))) d b
             | _ -> raise_v m "bytes: ~S does not fit" x)
         | _ -> raise_v m "bytes: ~S is not a valid index" i)
       | _ -> raise_v m "bytes: ~S is not a byte buffer" b)
    | _ -> prim_fallback p)
  | PStringBytes -> (match args with
    | [a] -> (match a with
      | VStr s -> let (l, m') = alloc m (OBytes s) in ret_to m' d (VBytes l)
      | _ -> raise_v m "shen-jit.string->bytes: ~S is not a string" a)
    | _ -> prim_fallback p)
  | PBytesString -> (match args with
    | [a; b; c] -> (match a with
      | VBytes l -> (match b, c with
        | VFix s, VFix n ->
          if s < 0 || n < 0 || length (bytes_of m l) < s + n
          then raise_v m "shen-jit.bytes->string: ~S is not a valid range" b
          else ret (VStr (firstn (to_nat n) (skipn (to_nat s) (bytes_of m l))))
        | _, _ -> raise_v m "shen-jit.bytes->string: ~S is not a valid range" b)
      | _ -> raise_v m "bytes: ~S is not a byte buffer" a)
    | _ -> prim_fallback p)
  | PCopyBytes -> (match args with
    | [a; b; c; ee; n] -> (match a, c with
      | VBytes la, VBytes lc -> (match b, ee, n with
        | VFix bi, VFix ei, VFix k ->
          if (bi < 0 || ei < 0 || k < 0)
             || (length (bytes_of m la) < bi + k || length (bytes_of m lc) < ei + k)
          then raise_v m "shen-jit.copy-bytes: ~S is not a valid count" n
          else let src = firstn (to_nat k) (skipn (to_nat ei) (bytes_of m lc)) in
            ret_to (put_bytes m la (splice (to_nat bi) src (bytes_of m la))) d a
        | _, _, _ -> raise_v m "shen-jit.copy-bytes: ~S is not a valid count" n)
      | VBytes _, _ -> raise_v m "bytes: ~S is not a byte buffer" c
      | _, _ -> raise_v m "bytes: ~S is not a byte buffer" a)
    | _ -> prim_fallback p)
  | PBitNot -> (match args with
    | [a] -> (match a with VFix x -> ret (VFix (zlnot x)) | _ -> raise_v m "bit operation: ~S is not an integer" a)
    | _ -> prim_fallback p)
  | PPopcount -> (match args with
    | [a] -> (match a with VFix x -> ret (VFix (popc 64 (word_of x))) | _ -> raise_v m "bit operation: ~S is not an integer" a)
    | _ -> prim_fallback p)
  | PClz -> (match args with
    | [a] -> (match a with
      | VFix x -> ret (VFix (if x = 0 then 62 else clz64 (word_of x)))
      | _ -> raise_v m "bit operation: ~S is not an integer" a)
    | _ -> prim_fallback p)
  | PCtz -> (match args with
    | [a] -> (match a with
      | VFix x -> ret (VFix (if x = 0 then 62 else ctz_go 64 (word_of x) 0 - 2))
      | _ -> raise_v m "bit operation: ~S is not an integer" a)
    | _ -> prim_fallback p)
  | PBswap32 -> (match args with
    | [a] -> (match a with
      | VFix x -> if x < 0 || 4294967296 <= x then raise_v m "shen-jit.bswap32: ~S does not fit in 32 bits" a
        else ret (VFix (le_read (rev (le_bytes 4 (to_nat x)))))
      | _ -> raise_v m "bit operation: ~S is not an integer" a)
    | _ -> prim_fallback p)
  | PBitAnd | PBitOr | PBitXor | PShiftLeft | PShiftRight | PRotate32 -> (match args with
    | [a; b] -> (match a, b with
      | VFix x, VFix y -> (match p with
        | PBitAnd -> ret (VFix (zland x y)) | PBitOr -> ret (VFix (zlor x y)) | PBitXor -> ret (VFix (zlxor x y))
        | _ ->
          if y < 0 || 63 < y then raise_v m "bit operation: ~S is not a valid shift" b else
          (match p with
           | PShiftLeft -> ret (VFix (of_word (u64 (zshiftl (word_of x) y))))
           | PShiftRight ->
             let s = if ztestbit (word_of x) 63 then word_of x - 18446744073709551616 else word_of x in
             ret (VFix (of_word (zland (u64 (zshiftr s y)) 18446744073709551612)))
           | _ ->
             if x < 0 || 4294967296 <= x then raise_v m "shen-jit.rotate32: ~S does not fit in 32 bits" a else
             let k = zland y 31 in
             ret (VFix (zland (zlor (zshiftl x k) (zshiftr x (zland (32 - k) 31))) 4294967295))))
      | VFix _, _ -> raise_v m "bit operation: ~S is not an integer" b
      | _, _ -> raise_v m "bit operation: ~S is not an integer" a)
    | _ -> prim_fallback p)
  | PDecimal -> (match args with
    | [s; ex] -> (match s, ex with
      | VStr x, VFix exv ->
        let (mant, own) = split_exp x [] in
        ret (VReal (parse_decimal mant (exv + own)))
      | _, _ -> raise_v m "shen-jit.decimal: ~S is not a string and an exponent" s)
    | _ -> prim_fallback p)
  | PPvar -> (match args with
    | [a] -> (match a with
      | VFix z -> if z < 0 || 72057594037927935 < z then raise_v m "shen-jit.pvar: ~S is not a valid offset" a
        else ret (VPvar z)
      | _ -> raise_v m "shen-jit.pvar: ~S is not a valid offset" a)
    | _ -> prim_fallback p)
  | PPvarp -> (match args with [a] -> isb (match a with VPvar _ -> true | _ -> false) | _ -> prim_fallback p)
  | PPvarOffset -> (match args with
    | [a] -> (match a with
      | VPvar z -> ret (VFix z) | _ -> raise_v m "shen-jit.pvar-offset: ~S is not a Prolog variable" a)
    | _ -> prim_fallback p)
  | PDeref -> (match args with
    | [a; b; mark] ->
      deref_go m d b mark (1 + (match b with VVec l -> length (vec_cells m l) | _ -> 0)) a
    | _ -> prim_fallback p)
  | PSamep -> (match args with
    | [a; b] -> (match same a b with Some r -> isb r | None -> MStuck RIdentity)
    | _ -> prim_fallback p)
  | PPointerp -> (match args with [_] -> isb false | _ -> prim_fallback p)
  | PRaiseCond -> (match args with [] -> raise_s m "cond: no clause applies" | _ -> prim_fallback p)
  | PGetTime -> (match args with
    | [a] -> (match a with
      | VSym s ->
        if s = s_run then MIO (JTime true) (fun r -> match r with
          | JTimeIs b -> set_stack m (swrite m d (VReal b)) | _ -> m)
        else if s = s_unix then MIO (JTime false) (fun r -> match r with
          | JTimeIs b -> set_stack m (swrite m d (VReal b)) | _ -> m)
        else raise_v m "get-time: ~S is not run or unix" a
      | _ -> raise_v m "get-time: ~S is not run or unix" a)
    | _ -> prim_fallback p)
  | POpen -> (match args with
    | [path; dir] ->
      (match path with
       | VStr ps ->
         let home = (match tget s__home_directory_ m.m_gval with Some (VStr h) -> h | _ -> []) in
         let go ds = MIO (JOpen (app home ps) ds) (fun r -> match r with
           | JOpened h -> let (l, m') = alloc m (OStream h ds true) in set_stack m' (swrite m' d (VStream l))
           | _ -> (match raise_v m "open: cannot open ~S" path with MTau m' -> m' | _ -> m)) in
         (match dir with
          | VSym s ->
            if s = s_out then go SOut
            else if s = s_in then go SIn
            else raise_v m "open: the direction ~S is not in or out" dir
          | _ -> raise_v m "open: the direction ~S is not in or out" dir)
       | _ -> raise_v m "open: ~S is not a string" path)
    | _ -> prim_fallback p)
  | PClose -> (match args with
    | [s] -> (match s with
      | VStream l -> (match tget l m.m_heap with
        | Some (OStream h dr true) ->
          let m1 = set_heap m (tset l (OStream h dr false) m.m_heap) in
          MIO (JClose h) (fun r -> match r with
            | JFailed -> (match raise_s m1 "close: the write failed" with MTau m' -> m' | _ -> m1)
            | _ -> set_stack m1 (swrite m1 d VNil))
        | _ -> ret VNil)
      | _ -> raise_v m "close: ~S is not a stream" s)
    | _ -> prim_fallback p)
  | PReadByte -> (match args with
    | [s] -> (match s with
      | VStream l -> (match tget l m.m_heap with
        | Some (OStream h SIn true) -> MIO (JRead h) (fun r -> match r with
          | JByte b -> set_stack m (swrite m d (VFix b))
          | _ -> set_stack m (swrite m d (VFix (-1))))
        | _ -> raise_v m "read-byte: ~S is not an open input stream" s)
      | _ -> raise_v m "read-byte: ~S is not an open input stream" s)
    | _ -> prim_fallback p)
  | PWriteByte -> (match args with
    | [b; s] -> (match s with
      | VStream l -> (match tget l m.m_heap with
        | Some (OStream h SOut true) -> (match b with
          | VFix z ->
            if 0 <= z && z <= 255
            then MIO (JWrite h (to_nat z)) (fun r -> match r with
              | JFailed -> (match raise_s m "write-byte: the write failed" with MTau m' -> m' | _ -> m)
              | _ -> set_stack m (swrite m d b))
            else raise_v m "write-byte: ~S is not a byte" b
          | _ -> raise_v m "write-byte: ~S is not a byte" b)
        | _ -> raise_v m "write-byte: ~S is not an open output stream" s)
      | _ -> raise_v m "write-byte: ~S is not an open output stream" s)
    | _ -> prim_fallback p)
  | PReadFile -> (match args with
    | [path; as_list] -> (match path with
      | VStr ps ->
        let home = (match tget s__home_directory_ m.m_gval with Some (VStr h) -> h | _ -> []) in
        MIO (JReadFile (app home ps)) (fun r -> match r with
          | JFile bs ->
            set_stack m (swrite m d (match as_list with
              | VBool true -> of_list (map #nat #val_ (fun (b : nat) -> VFix b) bs)
              | _ -> VStr bs))
          | _ -> (match raise_v m "open: cannot open ~S" path with MTau m' -> m' | _ -> m))
      | _ -> raise_v m "open: ~S is not a string" path)
    | _ -> prim_fallback p)
  | _ -> prim_fallback p

(* ---------- entering a procedure ---------- *)
let enter (e : env) (m : machine) (callee : val_) (count : nat) (st : tree val_) (fp : nat) (ks : list cont) : move =
  match callee with
  | VClo l -> (match tget l m.m_heap with
    | Some (OClo c _) ->
      let m' = set_ctl m st fp c (code_ins c) ks in
      let msg (_ : unit) : text = (match code_name c with
        | VSym s -> app (text_of_sym s) (app (t ": expected ") (app (z_digits (code_arity c))
                     (app (t (if code_arity c = 1 then " argument, got " else " arguments, got "))
                     (z_digits count))))
        | _ -> t "wrong number of arguments") in
      let checked (r : list instr) : move =
        if e.e_stack (fp + code_frame c) then raise_s m' "stack overflow" else MTau (set_rest m' r) in
      if count = code_arity c then checked (code_ins c)
      else (match code_entry c with
        | Some (n, lb) ->
          if count = n then
            (match find_label lb (code_ins c) with Some r -> checked r | None -> MStuck RBadLabel)
          else raise m' (msg ()) VCleared
        | None -> raise m' (msg ()) VCleared)
    | _ -> MStuck RBadCode)
  | _ -> MStuck RBadCode

let callee_named (m : machine) (f : pos) : either val_ move =
  match tget f m.m_gfun with
  | Some (VClo l) -> Inl (VClo l)
  | _ -> Inr (raise_v m "undefined function ~S" (VSym f))
let callee_value (m : machine) (a : nat) : either val_ move =
  match sread m (a + 1) with
  | Some (VClo l) -> Inl (VClo l)
  | Some VCleared | None -> Inr (raise_v m "undefined function ~S" VCleared)
  | Some v -> Inr (raise_v m "~S is not a function" v)

let do_call (e : env) (m : machine) (d a n : nat) (r : list instr) (cv : either val_ move) : move =
  match cv with
  | Inr mv -> mv
  | Inl callee ->
    let st = tset (skey (m.m_fp + a + 1)) callee m.m_stack in
    enter e m callee n st (m.m_fp + a) (mkCont m.m_code r d a :: m.m_conts)

let rec move_args (st : tree val_) (fp a : nat) (n : nat) (i : nat) : Tot (option (tree val_)) (decreases n) =
  if n = 0 then Some st else
  match tget (skey (fp + a + 2 + i)) st with
  | Some v -> move_args (tset (skey (fp + 2 + i)) v st) fp a (n - 1) (i + 1)
  | None -> None
let do_tail (e : env) (m : machine) (a n : nat) (cv : either val_ move) : move =
  match cv with
  | Inr mv -> mv
  | Inl callee ->
    (match (if a = 0 then Some m.m_stack else move_args m.m_stack m.m_fp a n 0) with
     | Some st -> enter e m callee n (tset (skey (m.m_fp + 1)) callee st) m.m_fp m.m_conts
     | None -> MStuck (RBadSlot a))

let read_op (m : machine) (o : operand) : option val_ = match o with
  | OSlot s -> sread m s
  | OConst k -> nth_error (code_consts m.m_code) k

let do_return (m : machine) (v : val_) : move =
  match m.m_conts with
  | [] -> MFinal (FReturn v) m
  | k :: ks ->
    let fp = nsub m.m_fp k.k_window in
    MTau (set_ctl m (tset (skey (fp + k.k_dst)) v m.m_stack) fp k.k_code k.k_rest ks)

(* ---------- one step ---------- *)
let next (e : env) (ptab : tree (prim & nat)) (m0 : machine) : move =
  match m0.m_rest with
  | [] -> MStuck RFallOff
  | i :: r ->
    let m = set_rest m0 r in
    match i with
    | IMove d s -> (match sread m s with
      | Some v -> MTau (set_stack m (swrite m d v)) | None -> MStuck (RBadSlot s))
    | IConst d k -> (match nth_error (code_consts m.m_code) k with
      | Some v -> MTau (set_stack m (swrite m d v)) | None -> MStuck RBadConst)
    | ICapture d c -> (match sread m 1 with
      | Some (VClo l) -> (match tget l m.m_heap with
        | Some (OClo _ caps) -> (match nth_error caps c with
          | Some v -> MTau (set_stack m (swrite m d v)) | None -> MStuck RBadCapture)
        | _ -> MStuck RBadCapture)
      | _ -> MStuck RBadCapture)
    | IClosure d c ss ->
      (match nth_error (code_codes m.m_code) c, all_some (map (sread m) ss) with
       | Some nc, Some caps ->
         if e.e_oom m.m_allocs then raise_s m "out of memory" else
         let (l, m') = alloc m (OClo nc caps) in MTau (set_stack m' (swrite m' d (VClo l)))
       | None, _ -> MStuck RBadCode
       | _, None -> MStuck (RBadSlot d))
    | IPrim d p ops ->
      (match all_some (map (read_op m) ops) with
       | None -> MStuck (RBadSlot d)
       | Some args ->
         if allocates p && e.e_oom m.m_allocs then raise_s m "out of memory"
         else prim_step e ptab m d p args)
    | ILabel _ | IInline _ _ | IEntry _ _ -> MTau m
    | IJump l -> (match find_label l (code_ins m.m_code) with
      | Some r' -> MTau (set_rest m r') | None -> MStuck RBadLabel)
    | IJumpIfFalse o l -> (match read_op m o with
      | Some (VBool true) -> MTau m
      | Some (VBool false) -> (match find_label l (code_ins m.m_code) with
        | Some r' -> MTau (set_rest m r') | None -> MStuck RBadLabel)
      | Some v -> raise_v m "~S is not a boolean" v
      | None -> MStuck (RBadSlot 0))
    | ICall d a f n | ICallSealed d a f n -> do_call e m d a n r (callee_named m f)
    | ICallValue d a n -> do_call e m d a n r (callee_value m a)
    | ITail a f n | ITailSealed a f n -> do_tail e m a n (callee_named m f)
    | ITailValue a n -> do_tail e m a n (callee_value m a)
    | IReturn o -> (match read_op m o with
      | Some v -> do_return m v | None -> MStuck (RBadSlot 0))
    | IPushHandler l ->
      (match find_label l (code_ins m.m_code) with
       | None -> MStuck RBadLabel
       | Some after ->
         let quiet = (match after with IException _ :: _ -> false | _ -> true) in
         MTau (set_handlers m ({ h_code = m.m_code; h_label = l; h_fp = m.m_fp; h_conts = m.m_conts; h_quiet = quiet } :: m.m_handlers)))
    | IPopHandler -> (match m.m_handlers with
      | _ :: hs -> MTau (set_handlers m hs) | [] -> MStuck RBadCode)
    | IException d -> MTau (set_stack m (swrite m d m.m_exn))
    | IJumpUnlessEntry s n l ->
      let jump (_ : unit) : move = (match find_label l (code_ins m.m_code) with
        | Some r' -> MTau (set_rest m r') | None -> MStuck RBadLabel) in
      (match sread m s with
       | Some (VClo c) -> (match tget c m.m_heap with
         | Some (OClo cd _) -> (match code_entry cd with
           | Some (x, _) -> if x = n then MTau m else jump ()
           | None -> jump ())
         | _ -> jump ())
       | Some _ -> jump ()
       | None -> MStuck (RBadSlot s))

(* ---------- running ---------- *)
let boot_code : code = Code VNil 0 None 2 [] [IReturn (OConst 0)] [] VNil
let empty_machine : machine = {
  m_stack = Leaf; m_fp = 0; m_code = boot_code; m_rest = []; m_conts = [];
  m_handlers = []; m_exn = VNil; m_heap = Leaf; m_next = 1;
  m_gval = Leaf; m_gfun = Leaf; m_sealed = Leaf; m_seal_user = false; m_allocs = 0 }

type result = | RDone : o:final -> m:machine -> result | RStuck : why:stuck -> result | RNeedsIO | ROutOfFuel

let rec run (e : env) (ptab : tree (prim & nat)) (fuel : nat) (m : machine) : Tot result (decreases fuel) =
  if fuel = 0 then ROutOfFuel else
  match next e ptab m with
  | MTau m' -> run e ptab (fuel - 1) m'
  | MIO _ _ -> RNeedsIO
  | MFinal o m' -> RDone o m'
  | MStuck w -> RStuck w

let start (e : env) (m : machine) (callee : val_) : move =
  let st = tset (skey 1) callee Leaf in
  enter e (set_handlers m []) callee 0 st 0 []
