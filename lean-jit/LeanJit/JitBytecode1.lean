import LeanJit.JitFloat
/-! Port of `rocq/JitBytecode.v`, part 1 (maps, symbols, values, code, equality, hash, text).
Rocq `positive` is `Pos` below: a wrapper on `Nat` holding `p - 1`, a bijection, so that map
keys and symbols compute with the kernel's GMP-backed `Nat` (README, "encodings"). -/
namespace JitBytecode
open JitFloat

abbrev text := List Nat
def t (s : String) : text := s.toList.map Char.toNat

-- ---------- positive ----------
structure Pos where
  pred : Nat
  deriving DecidableEq, Repr
def Pos.val (p : Pos) : Nat := p.pred + 1
def Pos.one : Pos := ⟨0⟩
def Pos.succ (p : Pos) : Pos := ⟨p.pred + 1⟩
def Pos.eqb (a b : Pos) : Bool := a.pred == b.pred
/-- A positive from its value (`n ≥ 1`). -/
def Pos.ofVal (n : Nat) : Pos := ⟨n - 1⟩

-- ---------- finite maps: binary tries, keyed as Rocq's `positive` (xH, xO, xI) ----------
inductive tree (A : Type) | Leaf | Node (l : tree A) (v : Option A) (r : tree A)
export tree (Leaf Node)

/-- Lookup by key value `k ≥ 1`: 1 is xH, even is xO, odd is xI. -/
def tgetN {A} (k : Nat) : tree A → Option A
  | Leaf => none
  | Node l v r => if k ≤ 1 then v else if k % 2 == 0 then tgetN (k / 2) l else tgetN (k / 2) r
/-- Update, recursing on a fuel bound `f ≥ k` (each step halves k). -/
def tsetN {A} : Nat → Nat → A → tree A → tree A
  | 0, _, _, m => m
  | f + 1, k, x, Leaf =>
    if k ≤ 1 then Node Leaf (some x) Leaf
    else if k % 2 == 0 then Node (tsetN f (k / 2) x Leaf) none Leaf
    else Node Leaf none (tsetN f (k / 2) x Leaf)
  | f + 1, k, x, Node l v r =>
    if k ≤ 1 then Node l (some x) r
    else if k % 2 == 0 then Node (tsetN f (k / 2) x l) v r
    else Node l v (tsetN f (k / 2) x r)
def tget {A} (k : Pos) (m : tree A) : Option A := tgetN k.val m
def tset {A} (k : Pos) (x : A) (m : tree A) : tree A := tsetN k.val k.val x m

-- ---------- symbols ----------
def sym_of_text (s : text) : Pos :=
  Pos.ofVal (s.foldl (fun acc b => acc * 256 + (if b == 0 then 256 else b)) 1)
def sym (s : String) : Pos := sym_of_text (t s)
def S_move := sym "move"
def S_const := sym "const"
def S_code := sym "code"
def S_defun := sym "defun"
def S_run := sym "run"
def S_unix := sym "unix"
def S_in := sym "in"
def S_out := sym "out"
def S_shen_fail_ := sym "shen.fail!"
def S__home_directory_ := sym "*home-directory*"
def text_of_sym_go : Nat → Int → text → text
  | 0, _, acc => acc
  | f + 1, p, acc => if p ≤ 1 then acc else
    let d := Z.rem (p - 1) 256 + 1
    text_of_sym_go f (Z.quot (p - d) 256) ((Z.rem d 256).toNat :: acc)
def text_of_sym (p : Pos) : text := text_of_sym_go 4096 (p.val : Int) []

-- ---------- values, code, heap ----------
inductive val
  | VFix (z : Int) | VReal (bits : Nat) | VSym (s : Pos) | VBool (b : Bool) | VNil
  | VCleared
  | VStr (s : text) | VPair (a d : val)
  | VVec (l : Pos) | VBytes (l : Pos) | VClo (l : Pos)
  | VExn (l : Pos) | VStream (l : Pos) | VPvar (off : Int)
  deriving DecidableEq, Repr
open val

inductive prim
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
  deriving DecidableEq, Repr
open prim

def prim_table : List (String × prim × Nat) :=
 [("+",PAdd,2),("-",PSub,2),("*",PMul,2),("/",PDiv,2),("<",PLt,2),(">",PGt,2),("<=",PLe,2),(">=",PGe,2)
 ,("=",PEq,2),("number?",PNumberp,1),("cons",PCons,2),("hd",PHd,1),("tl",PTl,1),("cons?",PConsp,1)
 ,("cn",PCn,2),("pos",PPos,2),("tlstr",PTlstr,1),("str",PStr,1),("string?",PStringp,1)
 ,("n->string",PNString,1),("string->n",PStringN,1),("intern",PIntern,1),("absvector",PAbsvector,1)
 ,("absvector?",PAbsvectorp,1),("<-address",PGetAddress,2),("address->",PSetAddress,3),("set",PSet,2)
 ,("value",PValue,1),("simple-error",PSimpleError,1),("error-to-string",PErrorToString,1)
 ,("eval-kl",PEvalKl,1),("get-time",PGetTime,1),("open",POpen,2),("close",PClose,1)
 ,("read-byte",PReadByte,1),("write-byte",PWriteByte,2),("char-stream?",PCharStreamp,1)
 ,("read-unit-string",PReadUnitString,1),("write-string",PWriteString,2)
 ,("shen-jit.install",PInstall,1),("shen-jit.symbol?",PSymbolp,1),("shen-jit.hash",PHash,2)
 ,("shen-jit.exit",PExit,1),("shen-jit.symbol-kind",PSymbolKind,1)
 ,("shen-jit.filled-vector",PFilledVector,2),("shen-jit.dict-find",PDictFind,2)
 ,("shen-jit.dict-put",PDictPut,3),("shen-jit.dict-remove",PDictRemove,2)
 ,("shen-jit.dict-entries",PDictEntries,1),("shen-jit.tagged?",PTaggedp,2)
 ,("shen-jit.sealed?",PSealedp,1),("shen-jit.sealing",PSealing,1),("shen-jit.inline-body",PInlineBody,1)
 ,("shen-jit.vector?",PVectorp,1),("shen-jit.absvector3",PAbsvector3,3),("shen-jit.quiet?",PQuietp,0)
 ,("shen-jit.mark-toplevel",PMarkToplevel,0),("shen-jit.trace-text",PTraceText,1)
 ,("shen-jit.backtrace",PBacktrace,0),("shen-jit.read-file",PReadFile,2),("shen-jit.integer?",PIntegerp,1)
 ,("shen-jit.append",PAppend,2),("shen-jit.arity?",PArityp,2),("shen-jit.inlined?",PInlinedp,2)
 ,("shen-jit.save-executable",PSaveExecutable,2),("shen-jit.bytes",PBytesNew,1),("shen-jit.bytes?",PBytesp,1)
 ,("shen-jit.bytes-length",PBytesLength,1),("shen-jit.u8",PU8,2),("shen-jit.u16",PU16,2),("shen-jit.u32",PU32,2)
 ,("shen-jit.u8!",PSetU8,3),("shen-jit.u16!",PSetU16,3),("shen-jit.u32!",PSetU32,3)
 ,("shen-jit.s32",PS32,2),("shen-jit.s64",PS64,2),("shen-jit.f32",PF32,2),("shen-jit.f64",PF64,2)
 ,("shen-jit.s32!",PSetS32,3),("shen-jit.s64!",PSetS64,3),("shen-jit.f32!",PSetF32,3),("shen-jit.f64!",PSetF64,3)
 ,("shen-jit.string->bytes",PStringBytes,1),("shen-jit.bytes->string",PBytesString,3)
 ,("shen-jit.copy-bytes",PCopyBytes,5),("shen-jit.bit-and",PBitAnd,2),("shen-jit.bit-or",PBitOr,2)
 ,("shen-jit.bit-xor",PBitXor,2),("shen-jit.bit-not",PBitNot,1),("shen-jit.shift-left",PShiftLeft,2)
 ,("shen-jit.shift-right",PShiftRight,2),("shen-jit.rotate32",PRotate32,2),("shen-jit.bswap32",PBswap32,1)
 ,("shen-jit.popcount",PPopcount,1),("shen-jit.clz",PClz,1),("shen-jit.ctz",PCtz,1),("shen-jit.decimal",PDecimal,2)
 ,("shen-jit.pvar",PPvar,1),("shen-jit.pvar?",PPvarp,1),("shen-jit.pvar-offset",PPvarOffset,1)
 ,("shen-jit.deref",PDeref,3),("shen-jit.same?",PSamep,2),("shen-jit.thread",PThread,1)
 ,("shen-jit.foreign",PForeign,2),("shen-jit.pointer?",PPointerp,1),("shen-jit.pointer-kind",PPointerKind,1)
 ,("shen-jit.pointer-address",PPointerAddress,1),("shen-jit.bytes->pointer",PBytesPointer,3)
 ,("shen-jit.pointer->string",PPointerString,1),("shen-jit.pointer->bytes",PPointerBytes,3)
 ,("shen-jit.errno",PErrno,0),("shen-jit.c-errno",PCErrno,0),("shen-jit.pointer-kill",PPointerKill,1)
 ,("shen-jit.pointer-sized",PPointerSized,2),("shen-jit.pointer!",PSetPointer,3)
 ,("shen-jit.pointer-guard",PPointerGuard,2),("shen-jit.pointer-owner",PPointerOwner,1)
 ,("shen-jit.pointers-dead",PPointersDead,0),("shen-jit.pointer-read-only",PPointerReadOnly,1)
 ,("shen-jit.collect",PCollect,0)
 ,("raise-cond",PRaiseCond,0)]

inductive operand | OSlot (s : Nat) | OConst (k : Nat) deriving DecidableEq, Repr
open operand
inductive instr
  | IMove (d s : Nat) | IConst (d k : Nat) | ICapture (d i : Nat)
  | IClosure (d c : Nat) (ss : List Nat)
  | IPrim (d : Nat) (p : prim) (ops : List operand)
  | ILabel (l : Nat) | IJump (l : Nat) | IJumpIfFalse (o : operand) (l : Nat)
  | ICall (d a : Nat) (f : Pos) (n : Nat) | ICallSealed (d a : Nat) (f : Pos) (n : Nat)
  | ICallValue (d a n : Nat)
  | ITail (a : Nat) (f : Pos) (n : Nat) | ITailSealed (a : Nat) (f : Pos) (n : Nat)
  | ITailValue (a n : Nat)
  | IReturn (o : operand) | IPushHandler (l : Nat) | IPopHandler | IException (d : Nat)
  | IEntry (n l : Nat) | IJumpUnlessEntry (s n l : Nat) | IInline (f : Pos) (n : Nat)
  deriving DecidableEq, Repr
open instr

inductive code
  | Code (c_name : val) (c_arity : Nat) (c_entry : Option (Nat × Nat)) (c_frame : Nat)
      (c_consts : List val) (c_ins : List instr) (c_codes : List code) (c_inline : val)
open code
def code_name : code → val | Code x _ _ _ _ _ _ _ => x
def code_arity : code → Nat | Code _ x _ _ _ _ _ _ => x
def code_entry : code → Option (Nat × Nat) | Code _ _ x _ _ _ _ _ => x
def code_frame : code → Nat | Code _ _ _ x _ _ _ _ => x
def code_consts : code → List val | Code _ _ _ _ x _ _ _ => x
def code_ins : code → List instr | Code _ _ _ _ _ x _ _ => x
def code_codes : code → List code | Code _ _ _ _ _ _ x _ => x
def code_inline : code → val | Code _ _ _ _ _ _ _ x => x

inductive stream_dir | SIn | SOut deriving DecidableEq
open stream_dir
inductive obj
  | OVec (cells : List val) | OBytes (bs : List Nat)
  | OClo (c : code) (caps : List val)
  | OExn (msg : text) (v : val)
  | OStream (handle : Nat) (d : stream_dir) (is_open : Bool)
open obj

structure cont where
  Cont ::
  k_code : code
  k_rest : List instr
  k_dst : Nat
  k_window : Nat
structure handler where
  Handler ::
  h_code : code
  h_label : Nat
  h_fp : Nat
  h_conts : List cont
  h_quiet : Bool

structure machine where
  m_stack : tree val
  m_fp : Nat
  m_code : code
  m_rest : List instr
  m_conts : List cont
  m_handlers : List handler
  m_exn : val
  m_heap : tree obj
  m_next : Pos
  m_gval : tree val
  m_gfun : tree val
  m_sealed : tree Unit
  m_seal_user : Bool
  m_allocs : Nat

structure env where
  e_oom : Nat → Bool
  e_stack : Nat → Bool
  e_hash : text → Int

inductive jreq
  | JOpen (path : text) (d : stream_dir) | JClose (h : Nat)
  | JRead (h : Nat) | JWrite (h : Nat) (b : Nat) | JTime (run : Bool) | JReadFile (path : text)
inductive jres
  | JOpened (h : Nat) | JFailed | JDone | JByte (b : Nat) | JEof | JTimeIs (bits : Nat) | JFile (bs : List Nat)

inductive stuck
  | RBadSlot (s : Nat)
  | RBadConst | RBadLabel | RFallOff | RBadCapture | RBadCode
  | RIdentity
  | RCyclic
  | RExcluded (p : prim)
  | RArgs
  deriving DecidableEq

inductive final | FReturn (v : val) | FError (e : val) | FExit (status : Int)
inductive move
  | MTau (m : machine) | MIO (q : jreq) (k : jres → machine)
  | MFinal (o : final) (m : machine) | MStuck (why : stuck)

-- ---------- small helpers ----------
def skey (n : Nat) : Pos := ⟨n⟩   -- N.succ_pos n, the positive n + 1
def sread (m : machine) (s : Nat) : Option val := tget (skey (m.m_fp + s)) m.m_stack
def swrite (m : machine) (s : Nat) (v : val) : tree val := tset (skey (m.m_fp + s)) v m.m_stack
def set_stack (m : machine) (st : tree val) : machine := { m with m_stack := st }
def set_rest (m : machine) (r : List instr) : machine := { m with m_rest := r }
def set_ctl (m : machine) (st : tree val) (fp : Nat) (c : code) (r : List instr) (ks : List cont) : machine :=
  { m with m_stack := st, m_fp := fp, m_code := c, m_rest := r, m_conts := ks }
def set_handlers (m : machine) (hs : List handler) : machine := { m with m_handlers := hs }
def set_exn (m : machine) (e : val) : machine := { m with m_exn := e }
def set_heap (m : machine) (h : tree obj) : machine := { m with m_heap := h }
def set_globals (m : machine) (gv gf : tree val) (se : tree Unit) (su : Bool) : machine :=
  { m with m_gval := gv, m_gfun := gf, m_sealed := se, m_seal_user := su }
def alloc (m : machine) (o : obj) : Pos × machine :=
  let l := m.m_next
  (l, { m with m_heap := tset l o m.m_heap, m_next := l.succ, m_allocs := m.m_allocs + 1 })

def vlist : val → Option (List val)
  | VNil => some []
  | VPair a d => (vlist d).map (a :: ·)
  | _ => none
def of_list : List val → val
  | [] => VNil
  | a :: d => VPair a (of_list d)

def fix_min : Int := -2305843009213693952
def fix_max : Int := 2305843009213693951
def fix_fits (z : Int) : Bool := decide (fix_min ≤ z) && decide (z ≤ fix_max)
def is_number : val → Bool | VFix _ | VReal _ => true | _ => false
def number : val → Nat | VFix z => of_Z z | VReal b => b | _ => 0

def compare_fix_real (i : Int) (b : Nat) : Option Ordering :=
  match classify b with
  | .CNan => none
  | .CInf neg => some (if neg then .gt else .lt)
  | _ => match ratio b with
    | some (neg, n, den) => some (Z.compare (i * den) (if neg then - n else n))
    | none => none

-- ---------- identity ----------
def same (a b : val) : Option Bool := match a, b with
  | VFix x, VFix y => some (x == y) | VSym x, VSym y => some (x.eqb y)
  | VBool x, VBool y => some (x == y) | VNil, VNil => some true
  | VCleared, VCleared => some true | VPvar x, VPvar y => some (x == y)
  | VVec x, VVec y | VBytes x, VBytes y | VClo x, VClo y | VExn x, VExn y | VStream x, VStream y =>
    some (x.eqb y)
  | VPair _ _, VPair _ _ | VStr _, VStr _ | VReal _, VReal _ => none
  | _, _ => some false

def text_eqb : text → text → Bool
  | [], [] => true
  | x :: a, y :: b => (x == y) && text_eqb a b
  | _, _ => false

-- ---------- = (sj_equal) ----------
inductive eqr | EqT | EqF | EqIdentity | EqCycle deriving DecidableEq
open eqr
def eq_list (f : val → val → eqr) : List val → List val → eqr
  | [], [] => EqT
  | x :: xs, y :: ys => match f x y with | EqT => eq_list f xs ys | r => r
  | _, _ => EqF
/-- The inner `fix go` of `eq_val`, with the deeper call passed in. -/
def eq_val_go (h : tree obj) (rec : val → val → eqr) : val → val → eqr
  | VPair a1 a2, VPair b1 b2 => match eq_val_go h rec a1 b1 with | EqT => eq_val_go h rec a2 b2 | r => r
  | VFix x, VFix y => if x == y then EqT else EqF
  | VFix x, VReal y => match compare_fix_real x y with | some .eq => EqT | _ => EqF
  | VReal x, VFix y => match compare_fix_real y x with | some .eq => EqT | _ => EqF
  | VReal x, VReal y => if is_nan x && is_nan y then EqIdentity else if eqv x y then EqT else EqF
  | VStr x, VStr y => if text_eqb x y then EqT else EqF
  | VSym x, VSym y => if x.eqb y then EqT else EqF
  | VBool x, VBool y => if x == y then EqT else EqF
  | VNil, VNil | VCleared, VCleared => EqT
  | VPvar x, VPvar y => if x == y then EqT else EqF
  | VClo x, VClo y | VExn x, VExn y | VStream x, VStream y => if x.eqb y then EqT else EqF
  | VVec x, VVec y =>
    if x.eqb y then EqT else
    match tget x h, tget y h with
    | some (OVec xs), some (OVec ys) => eq_list rec xs ys
    | _, _ => EqCycle
  | VBytes x, VBytes y =>
    if x.eqb y then EqT else
    match tget x h, tget y h with
    | some (OBytes xs), some (OBytes ys) => if text_eqb xs ys then EqT else EqF
    | _, _ => EqCycle
  | _, _ => EqF
def eq_val (h : tree obj) : Nat → val → val → eqr
  | 0 => fun _ _ => EqCycle
  | f + 1 => eq_val_go h (eq_val h f)
def eq_fuel : Nat := 4096

-- ---------- hash ----------
def u64 (z : Int) : Int := Z.land z 18446744073709551615
def mix (x : Int) : Int :=
  let x := Z.lxor x (Z.shiftr x 33)
  let x := u64 (x * 18397679294719823053)
  let x := Z.lxor x (Z.shiftr x 33)
  let x := u64 (x * 14181476777654086739)
  Z.lxor x (Z.shiftr x 33)
def special_word (n : Int) : Int := n * 8 + 2
/-- The inner `fix walk` of `hash_go`, with `hash_go E h f` passed in as `hg`. -/
def hash_walk (hg : val → Int → Int × Int) : Nat → val → Int → Int → Int × Int
  | 0, _, acc, budget => (acc, budget)
  | fl + 1, x, acc, budget => match x with
    | VPair a d =>
      if budget ≤ 0 then let (r, b) := hg x budget; (mix (Z.lxor acc r), b)
      else let (r, b) := hg a budget; hash_walk hg fl d (mix (Z.lxor acc r)) b
    | _ => let (r, b) := hg x budget; (mix (Z.lxor acc r), b)
def hash_go (E : env) (h : tree obj) : Nat → val → Int → Int × Int
  | 0, _, budget => (0, budget)
  | f + 1, v, budget =>
    let budget := budget - 1
    if budget < 0 then (0, budget) else
    match v with
    | VFix z => (mix (u64 z), budget)
    | VReal b =>
      match to_Z_exact b with
      | some z => if Z.abs z < 9200000000000000000 then (mix (u64 z), budget) else (mix (b : Int), budget)
      | none => (mix (b : Int), budget)
    | VSym s => (E.e_hash (text_of_sym s), budget)
    | VPair _ _ => hash_walk (hash_go E h f) 300 v 112 budget
    | VStr s => (E.e_hash s, budget)
    | VBytes l => match tget l h with | some (OBytes bs) => (E.e_hash bs, budget) | _ => (0, budget)
    | VVec l => match tget l h with
      | some (OVec cells) =>
        cells.foldl (fun st c => let (acc, b) := st
          if b ≤ 0 then st else let (r, b') := hash_go E h f c b; (mix (Z.lxor acc r), b'))
          (118, budget)
      | _ => (0, budget)
    | VNil => (mix (special_word 0), budget)
    | VBool false => (mix (special_word 1), budget)
    | VBool true => (mix (special_word 2), budget)
    | VCleared => (mix (special_word 3), budget)
    | VPvar off => (mix (off * 256 + 250), budget)
    | VClo _ => (mix 80, budget)
    | VExn _ => (mix 10, budget)
    | VStream _ => (mix 9, budget)
def sj_hash (E : env) (h : tree obj) (v : val) : Int := (hash_go E h 300 v 256).1

-- ---------- text of values ----------
def fmt_real (b : Nat) : text := format_real b
def to_string_atom : val → text
  | VFix z => z_text z | VBool true => t "true" | VBool false => t "false" | VNil => t "()"
  | VPvar o => t "Var" ++ z_digits o | VSym s => text_of_sym s
  | VStr s => [34] ++ s ++ [34] | VReal b => fmt_real b
  | VPair _ _ => t "#<pair>" | VClo _ => t "#<procedure>" | VVec _ => t "#<absvector>"
  | VStream _ => t "#<stream>" | VBytes _ => t "#<bytes>" | VExn _ => t "#<exception>"
  | VCleared => t "#<value>"

def sep_join (items : List text) : text :=
  match items with | [] => [] | x :: r => x ++ r.flatMap (fun i => [32] ++ i)
def is_fail : val → Bool | VSym s => s.eqb S_shen_fail_ | _ => false
def show_vec (sh : val → text) (cells : List val) : text :=
  let cut (l : text) := l.take 61
  match cells with
  | VFix z :: rest =>
    if decide (0 ≤ z) && decide (z < (cells.length : Int)) then
      t "<" ++ cut (sep_join (((rest.take z.toNat).take 61).map (fun c => if is_fail c then t "..." else cut (sh c)))) ++ t ">"
    else t "<<" ++ cut (sep_join ((cells.take 61).map (fun c => cut (sh c)))) ++ t ">>"
  | _ => t "<<" ++ cut (sep_join ((cells.take 61).map (fun c => cut (sh c)))) ++ t ">>"

/-- The inner `fix tail` of `show`, with `show h f` passed in as `sh`. -/
def show_tail (sh : val → text) : Nat → val → text
  | 0, _ => []
  | fl + 1, x => match x with
    | VPair a d => t " " ++ sh a ++ show_tail sh fl d
    | VNil => []
    | x => t " | " ++ sh x
def «show» (h : tree obj) : Nat → val → text
  | 0, _ => []
  | f + 1, v => match v with
    | VPair a d => t "[" ++ «show» h f a ++ show_tail («show» h f) 64 d ++ t "]"
    | VVec l => match tget l h with
      | some (OVec [VSym s, a, b]) =>
        if text_eqb (text_of_sym s) (t "shen.tuple")
        then t "(@p " ++ «show» h f a ++ t " " ++ «show» h f b ++ t ")"
        else show_vec («show» h f) [VSym s, a, b]
      | some (OVec cells) => show_vec («show» h f) cells
      | _ => t "#<value>"
    | VStr s => [34] ++ s ++ [34]
    | VNil => t "[]"
    | VClo _ => t "#<procedure>" | VStream _ => t "#<stream>" | VBytes _ => t "#<bytes>"
    | VExn _ => t "#<exception>" | VCleared => t "#<value>"
    | x => to_string_atom x

def show_cut (h : tree obj) (v : val) : text :=
  let s := «show» h 64 v
  if s.length ≤ 60 then s else s.take 60 ++ t "..."

def subst_tilde : text → text → Option text
  | 126 :: 83 :: r, rep => some (rep ++ r)
  | c :: r, rep => (subst_tilde r rep).map (c :: ·)
  | [], _ => none
def exception_text (h : tree obj) (msg : text) (v : val) : text := match v with
  | VCleared => msg
  | _ => let s := show_cut h v
    match subst_tilde msg s with | some r => r | none => msg ++ [32] ++ s

end JitBytecode
