import LeanJit.JitBytecode2
/-! Port of `rocq/JitBytecode.v`, part 3 (primitives, calls, one step, running). Rocq's local
`fix`es inside `prim_step` (put_in, rm, walk, grow's go, deref's go, decimal's split) are
top-level helpers here, each given what it closes over. -/
namespace JitBytecode
open JitFloat val prim operand instr code obj stream_dir move final stuck eqr jreq jres

-- ---------- primitives ----------
def symbol_char (c : Nat) : Bool :=
  (decide (97 ≤ c) && decide (c ≤ 122)) || (decide (65 ≤ c) && decide (c ≤ 90)) || (decide (48 ≤ c) && decide (c ≤ 57))
  || (t "=-*/+_?$!@~.><&%'#`").any (c == ·)
def name_kind (s : text) : Int := match s with
  | [c] => if (t "{}:;,").any (c == ·) then 1
           else if decide (48 ≤ c) && decide (c ≤ 57) then 0
           else if symbol_char c then (if decide (65 ≤ c) && decide (c ≤ 90) then 2 else 1) else 0
  | [] => 0
  | c :: _ =>
    if decide (48 ≤ c) && decide (c ≤ 57) then 0
    else if s.all symbol_char then (if decide (65 ≤ c) && decide (c ≤ 90) then 2 else 1) else 0

def replace {A} : Nat → A → List A → List A
  | 0, x, _ :: r => x :: r
  | n + 1, x, y :: r => y :: replace n x r
  | _, _, [] => []

def le_read : List Nat → Nat | [] => 0 | b :: r => b + 256 * le_read r
def le_bytes : Nat → Nat → List Nat
  | 0, _ => [] | w + 1, x => (x &&& 255) :: le_bytes w (x >>> 8)
def splice {A} (at_ : Nat) (src dst : List A) : List A :=
  dst.take at_ ++ src ++ dst.drop (at_ + src.length)

def word_of (z : Int) : Int := u64 (z * 4)
def of_word (w : Int) : Int :=
  let s := if Z.testbit w 63 then w - 18446744073709551616 else w
  Z.div s 4
def popc : Nat → Int → Int
  | 0, _ => 0 | f + 1, w => if w == 0 then 0 else Z.land w 1 + popc f (Z.shiftr w 1)
def clz64 (w : Int) : Int := 63 - Z.log2 w
def ctz_go : Nat → Int → Int → Int
  | 0, _, n => n | f + 1, w, n => if Z.testbit w 0 then n else ctz_go f (Z.shiftr w 1) (n + 1)

def vec_cells (m : machine) (l : Pos) : List val :=
  match tget l m.m_heap with | some (OVec c) => c | _ => []
def put_vec (m : machine) (l : Pos) (c : List val) : machine := set_heap m (tset l (OVec c) m.m_heap)

def dict_parts (m : machine) (d : val) : Option (Pos × val × Int × Pos × List val) :=
  match d with
  | VVec l => match vec_cells m l with
    | [tag, VFix n, VVec b] =>
      if n < 0 then none else
      let bs := vec_cells m b
      let len := bs.length
      if decide (0 < len) && ((len &&& (len - 1)) == 0)
      then some (l, tag, n, b, bs) else none
    | _ => none
  | _ => none
def bucket_index (E : env) (m : machine) (k : val) (len : Nat) : Nat :=
  (Z.land (sj_hash E m.m_heap k) ((len : Int) - 1)).toNat
def bucket_find (h : tree obj) (k : val) : val → Option (Option (val × val))
  | VNil => some none
  | VPair (VPair kk vv) r =>
    match eq_val h eq_fuel kk k with
    | EqT => some (some (kk, vv))
    | EqF => bucket_find h k r
    | _ => none
  | _ => none

def bytes_of (m : machine) (l : Pos) : List Nat :=
  match tget l m.m_heap with | some (OBytes b) => b | _ => []
def put_bytes (m : machine) (l : Pos) (b : List Nat) : machine := set_heap m (tset l (OBytes b) m.m_heap)

def allocates : prim → Bool
  | PAdd | PSub | PMul | PDiv | PCons | PCn | PTlstr | PStr | PAbsvector | PFilledVector | PAbsvector3
  | PAppend | PBytesNew | PStringBytes | PBytesString | PDictPut | PDictEntries | PDecimal | PPos | PNString
  | PGetTime | POpen | PReadFile => true
  | _ => false

def is_excluded : prim → Bool
  | PMarkToplevel | PTraceText | PBacktrace | PSaveExecutable | PThread | PForeign
  | PPointerKind | PPointerAddress | PBytesPointer | PPointerString | PPointerBytes | PErrno | PCErrno
  | PPointerKill
  | PS32 | PS64 | PF32 | PF64 | PSetS32 | PSetS64 | PSetF32 | PSetF64
  | PPointerSized | PSetPointer | PPointerGuard | PPointerOwner | PPointersDead | PPointerReadOnly => true
  | _ => false

-- the local fixes of prim_step
def dict_put_in (h : tree obj) (k v : val) : val → val
  | VPair (VPair kk vv) r =>
    match eq_val h eq_fuel kk k with
    | EqT => VPair (VPair kk v) r | _ => VPair (VPair kk vv) (dict_put_in h k v r)
  | x => x
def dict_rm (h : tree obj) (k : val) : val → val
  | VPair (VPair kk vv) r =>
    match eq_val h eq_fuel kk k with
    | EqT => r | _ => VPair (VPair kk vv) (dict_rm h k r)
  | x => x
def dict_walk : val → val → val
  | VPair (VPair kk vv) r, acc => dict_walk r (VPair (VPair kk vv) acc)
  | _, acc => acc
def grow_go (E : env) (m : machine) (len : Nat) : val → List val → List val
  | VPair (VPair kk vv) r, acc =>
    let j := bucket_index E m kk len
    let cur := match acc[j]? with | some x => x | none => VNil
    grow_go E m len r (replace j (VPair (VPair kk vv) cur) acc)
  | _, acc => acc
def decimal_split : text → text → text × Int
  | 101 :: r, acc =>
    let (neg, ds) := match r with | 45 :: q => (true, q) | 43 :: q => (false, q) | _ => (false, r)
    let (v, _, _) := scan_digits ds 0 0
    (acc.reverse, if neg then - v else v)
  | c :: r, acc => decimal_split r (c :: acc)
  | [], acc => (acc.reverse, 0)

def prim_step (E : env) (ptab : tree (prim × Nat)) (m : machine) (d : Nat) (p : prim) (args : List val) : move :=
  let ret := ret_to m d
  let isb := boolean m d
  match p, args with
  | PAdd, [a, b] | PSub, [a, b] | PMul, [a, b] | PDiv, [a, b] =>
    if !(is_number a) then raise_v m "~S is not a number" a
    else if !(is_number b) then raise_v m "~S is not a number" b
    else if (match p, b with
         | PDiv, VFix z => z == 0 | PDiv, VReal r => is_zero r | _, _ => false)
    then raise_s m "division by zero"
    else match a, b with
    | VFix x, VFix y =>
      match p with
      | PDiv =>
        if !(Z.rem x y == 0) then ret (VReal (div (of_Z x) (of_Z y)))
        else let r := Z.quot x y; if fix_fits r then ret (VFix r) else raise_s m "integer overflow"
      | _ =>
        let r := match p with | PAdd => x + y | PSub => x - y | _ => x * y
        if fix_fits r then ret (VFix r) else raise_s m "integer overflow"
    | _, _ =>
      let x := number a
      let y := number b
      ret (VReal (match p with | PAdd => add x y | PSub => sub x y | PMul => mul x y | _ => div x y))
  | PLt, [a, b] | PGt, [a, b] | PLe, [a, b] | PGe, [a, b] =>
    if !(is_number a) then raise_v m "~S is not a number" a
    else if !(is_number b) then raise_v m "~S is not a number" b
    else match a, b with
    | VFix x, VFix y => isb (match p with
        | PLt => decide (x < y) | PGt => decide (x > y) | PLe => decide (x ≤ y) | _ => decide (x ≥ y))
    | VFix x, VReal r => isb (match compare_fix_real x r, p with
        | some .lt, PLt | some .lt, PLe | some .gt, PGt | some .gt, PGe | some .eq, PLe | some .eq, PGe => true
        | _, _ => false)
    | VReal r, VFix y => isb (match compare_fix_real y r, p with
        | some .gt, PLt | some .gt, PLe | some .lt, PGt | some .lt, PGe | some .eq, PLe | some .eq, PGe => true
        | _, _ => false)
    | _, _ =>
      let x := number a
      let y := number b
      isb (match p with | PLt => lt x y | PGt => gt x y | PLe => le x y | _ => ge x y)
  | PEq, [a, b] => match eq_val m.m_heap eq_fuel a b with
    | EqT => isb true | EqF => isb false
    | EqIdentity => MStuck RIdentity | EqCycle => MStuck RCyclic
  | PNumberp, [a] => isb (is_number a)
  | PCollect, [] => isb true
  | PCons, [a, b] => ret (VPair a b)
  | PHd, [v] => match v with | VPair a _ => ret a | _ => raise_v m "hd: ~S is not a pair" v
  | PTl, [v] => match v with | VPair _ b => ret b | _ => raise_v m "tl: ~S is not a pair" v
  | PConsp, [v] => isb (match v with | VPair _ _ => true | _ => false)
  | PStringp, [v] => isb (match v with | VStr _ => true | _ => false)
  | PAbsvector, [v] => match v with
    | VFix n => if n < 0 || decide (281474976710656 ≤ n) then raise_v m "absvector: ~S is not a valid length" v else
      let (l, m') := alloc m (OVec (List.replicate n.toNat (VSym S_shen_fail_))); ret_to m' d (VVec l)
    | _ => raise_v m "absvector: ~S is not a valid length" v
  | PAbsvectorp, [v] => isb (match v with | VVec _ => true | _ => false)
  | PGetAddress, [v, i] => match v with
    | VVec l => match i with
      | VFix z => if z < 0 then raise_v m "<-address: ~S is not a valid index" i else
        match (vec_cells m l)[z.toNat]? with
        | some x => ret x | none => raise_v m "<-address: ~S is not a valid index" i
      | _ => raise_v m "<-address: ~S is not a valid index" i
    | _ => raise_v m "<-address: ~S is not an absvector" v
  | PSetAddress, [v, i, x] => match v with
    | VVec l => match i with
      | VFix z =>
        if z < 0 || decide ((vec_cells m l).length ≤ z.toNat)
        then raise_v m "address->: ~S is not a valid index" i
        else ret_to (put_vec m l (replace z.toNat x (vec_cells m l))) d v
      | _ => raise_v m "address->: ~S is not a valid index" i
    | _ => raise_v m "address->: ~S is not an absvector" v
  | PSet, [a, b] => match a with
    | VSym s => ret_to (set_globals m (tset s b m.m_gval) m.m_gfun m.m_sealed m.m_seal_user) d b
    | _ => raise_v m "set: ~S is not a symbol" a
  | PValue, [a] => match a with
    | VSym s => match tget s m.m_gval with
      | some VCleared | none => raise_v m "~S has no value" a
      | some v => ret v
    | _ => raise_v m "value: ~S is not a symbol" a
  | PSimpleError, [a] => match a with
    | VStr s => raise m s VCleared
    | _ => raise_v m "simple-error: ~S is not a string" a
  | PErrorToString, [a] => match a with
    | VExn l => match tget l m.m_heap with
      | some (OExn msg v) => ret (VStr (exception_text m.m_heap msg v))
      | _ => MStuck RBadCode
    | _ => raise_v m "error-to-string: ~S is not an exception" a
  | PCn, [a, b] => match a, b with
    | VStr x, VStr y => ret (VStr (x ++ y))
    | VStr _, _ => raise_v m "cn: ~S is not a string" b
    | _, _ => raise_v m "cn: ~S is not a string" a
  | PPos, [a, b] => match a with
    | VStr s => match b with
      | VFix z => if z < 0 then raise_v m "pos: ~S is not a valid index" b else
        match s[z.toNat]? with
        | some c => ret (VStr [c]) | none => raise_v m "pos: ~S is not a valid index" b
      | _ => raise_v m "pos: ~S is not a valid index" b
    | _ => raise_v m "pos: ~S is not a string" a
  | PTlstr, [a] => match a with
    | VStr (_ :: r) => ret (VStr r)
    | _ => raise_v m "tlstr: ~S is not a non-empty string" a
  | PStr, [a] => ret (VStr (to_string_atom a))
  | PNString, [a] => match a with
    | VFix z => if decide (0 ≤ z) && decide (z ≤ 255) then ret (VStr [z.toNat])
                else raise_v m "n->string: ~S is not a byte" a
    | _ => raise_v m "n->string: ~S is not a byte" a
  | PStringN, [a] => match a with
    | VStr (c :: _) => ret (VFix (c : Int))
    | _ => raise_v m "string->n: ~S is not a non-empty string" a
  | PIntern, [a] => match a with
    | VStr s => if text_eqb s (t "true") then ret (VBool true)
                else if text_eqb s (t "false") then ret (VBool false)
                else ret (VSym (sym_of_text s))
    | _ => raise_v m "intern: ~S is not a string" a
  | PEvalKl, [_] => raise_s m "eval-kl is lowered as a call to shen-jit.eval-kl"
  | PCharStreamp, [_] => isb false
  | PReadUnitString, [_] | PWriteString, [_, _] => raise_s m "character streams are not supported"
  | PInstall, [form] => install ptab m d form
  | PSymbolp, [a] => isb (match a with | VSym _ => true | _ => false)
  | PHash, [a, b] => match b with
    | VFix n => if n ≤ 0 then raise_v m "hash: ~S is not a valid bound" b else
      let h := Z.rem (sj_hash E m.m_heap a) n; ret (VFix (if h == 0 then 1 else h))
    | _ => raise_v m "hash: ~S is not a valid bound" b
  | PExit, [a] => match a with
    | VFix z => if decide (0 ≤ z) && decide (z ≤ 255) then MFinal (FExit z) m
                else raise_v m "~S is not an exit status" a
    | _ => raise_v m "~S is not an exit status" a
  | PSymbolKind, [a] => ret (VFix (match a with | VSym s => name_kind (text_of_sym s) | _ => 0))
  | PFilledVector, [a, x] => match a with
    | VFix n => if n < 0 || decide (281474976710656 ≤ n) then raise_v m "shen-jit.filled-vector: ~S is not a valid length" a else
      let (l, m') := alloc m (OVec (List.replicate n.toNat x)); ret_to m' d (VVec l)
    | _ => raise_v m "shen-jit.filled-vector: ~S is not a valid length" a
  | PDictFind, [dv, k] => match dict_parts m dv with
    | none => raise_v m "~S is not a dictionary" dv
    | some (_, _, _, _, bs) =>
      match bs[bucket_index E m k bs.length]? with
      | some c => match bucket_find m.m_heap k c with
        | some (some (kk, vv)) => ret (VPair kk vv)
        | some none => ret VNil
        | none => raise_v m "~S is not a dictionary" dv
      | none => raise_v m "~S is not a dictionary" dv
  | PDictPut, [dv, k, v] => match dict_parts m dv with
    | none => raise_v m "~S is not a dictionary" dv
    | some (l, tag, n, b, bs) =>
      let i := bucket_index E m k bs.length
      let c := match bs[i]? with | some c => c | none => VNil
      match bucket_find m.m_heap k c with
      | none => raise_v m "~S is not a dictionary" dv
      | some (some _) => ret_to (put_vec m b (replace i (dict_put_in m.m_heap k v c) bs)) d v
      | some none =>
        let bs' := replace i (VPair (VPair k v) c) bs
        let m1 := put_vec m b bs'
        let n' := n + 1
        if (bs.length : Int) < n' then
          let len := 2 * bs.length
          let fresh := (vec_cells m1 b).foldl (fun acc cell_list => grow_go E m len cell_list acc)
            (List.replicate len VNil)
          let (nb, m2) := alloc m1 (OVec fresh)
          ret_to (put_vec m2 l [tag, VFix n', VVec nb]) d v
        else ret_to (put_vec m1 l [tag, VFix n', VVec b]) d v
  | PDictRemove, [dv, k] => match dict_parts m dv with
    | none => raise_v m "~S is not a dictionary" dv
    | some (l, tag, n, b, bs) =>
      let i := bucket_index E m k bs.length
      let c := match bs[i]? with | some c => c | none => VNil
      match bucket_find m.m_heap k c with
      | none => raise_v m "~S is not a dictionary" dv
      | some none => ret k
      | some (some _) => ret_to (put_vec (put_vec m b (replace i (dict_rm m.m_heap k c) bs)) l [tag, VFix (n - 1), VVec b]) d k
  | PDictEntries, [dv] => match dict_parts m dv with
    | none => raise_v m "~S is not a dictionary" dv
    | some (_, _, _, _, bs) => ret (bs.foldl (fun acc c => dict_walk c acc) VNil)
  | PTaggedp, [a, b] => match a with
    | VVec l => match vec_cells m l with
      | x :: _ => match same x b with | some r => isb r | none => MStuck RIdentity
      | [] => isb false
    | _ => isb false
  | PSealedp, [a] => match a with
    | VSym s => isb (match tget s m.m_sealed with
      | some _ => true
      | none => m.m_seal_user && (match tget s m.m_gfun with | some (VClo _) => false | _ => true))
    | _ => isb false
  | PSealing, [a] => match a with
    | VBool b => ret_to (set_globals m m.m_gval m.m_gfun m.m_sealed b) d a
    | _ => raise_v m "~S is not a boolean" a
  | PInlineBody, [a] => match a with
    | VSym s => match tget s m.m_gfun with
      | some (VClo l) => match tget l m.m_heap with
        | some (OClo c _) => ret (code_inline c) | _ => ret VNil
      | _ => ret VNil
    | _ => ret VNil
  | PVectorp, [a] => match a with
    | VVec l => match vec_cells m l with
      | VFix z :: _ => isb (decide (0 ≤ z))
      | VReal r :: _ => isb (ge r 0)
      | _ => isb false
    | _ => isb false
  | PAbsvector3, [a, b, c] => let (l, m') := alloc m (OVec [a, b, c]); ret_to m' d (VVec l)
  | PQuietp, [] => isb (match m.m_handlers with | h :: _ => h.h_quiet | [] => false)
  | PIntegerp, [a] => isb (match a with
    | VFix _ => true
    | VReal r => match to_Z_exact r with | some _ => true | none => false
    | _ => false)
  | PAppend, [a, b] => match vlist a with
    | some l => ret (l.foldr VPair b)
    | none => raise_s m "attempt to append a non-list"
  | PArityp, [a, b] => match a, b with
    | VSym s, VFix n => match tget s m.m_gfun with
      | some (VClo l) => match tget l m.m_heap with
        | some (OClo c _) => isb ((code_arity c : Int) == n) | _ => isb false
      | _ => isb false
    | _, _ => isb false
  | PInlinedp, [a, b] => match a with
    | VSym s => match tget s m.m_gfun with
      | some (VClo l) => match tget l m.m_heap with
        | some (OClo c _) =>
          match eq_val m.m_heap eq_fuel (code_inline c) b with
          | EqT => isb true | EqF => isb false | EqIdentity => MStuck RIdentity | EqCycle => MStuck RCyclic
        | _ => isb false
      | _ => isb false
    | _ => isb false
  | PBytesNew, [a] => match a with
    | VFix n => if n < 0 || decide (281474976710656 ≤ n) then raise_v m "shen-jit.bytes: ~S is not a valid length" a else
      let (l, m') := alloc m (OBytes (List.replicate n.toNat 0)); ret_to m' d (VBytes l)
    | _ => raise_v m "shen-jit.bytes: ~S is not a valid length" a
  | PBytesp, [a] => isb (match a with | VBytes _ => true | _ => false)
  | PBytesLength, [a] => match a with
    | VBytes l => ret (VFix ((bytes_of m l).length : Int))
    | _ => raise_v m "bytes: ~S is not a byte buffer" a
  | PU8, [b, i] | PU16, [b, i] | PU32, [b, i] =>
    let w : Nat := match p with | PU8 => 1 | PU16 => 2 | _ => 4
    match b with
    | VBytes l => match i with
      | VFix z =>
        if z < 0 || ((bytes_of m l).length : Int) < z + (w : Int)
        then raise_v m "bytes: ~S is not a valid index" i
        else ret (VFix (le_read (((bytes_of m l).drop z.toNat).take w) : Int))
      | _ => raise_v m "bytes: ~S is not a valid index" i
    | _ => raise_v m "bytes: ~S is not a byte buffer" b
  | PSetU8, [b, i, x] | PSetU16, [b, i, x] | PSetU32, [b, i, x] =>
    let w : Nat := match p with | PSetU8 => 1 | PSetU16 => 2 | _ => 4
    match b with
    | VBytes l => match i with
      | VFix z =>
        if z < 0 || ((bytes_of m l).length : Int) < z + (w : Int)
        then raise_v m "bytes: ~S is not a valid index" i
        else match x with
          | VFix y =>
            if y < 0 || decide (Z.shiftl 1 (8 * (w : Int)) ≤ y) then raise_v m "bytes: ~S does not fit" x
            else ret_to (put_bytes m l (splice z.toNat (le_bytes w y.toNat) (bytes_of m l))) d b
          | _ => raise_v m "bytes: ~S does not fit" x
      | _ => raise_v m "bytes: ~S is not a valid index" i
    | _ => raise_v m "bytes: ~S is not a byte buffer" b
  | PStringBytes, [a] => match a with
    | VStr s => let (l, m') := alloc m (OBytes s); ret_to m' d (VBytes l)
    | _ => raise_v m "shen-jit.string->bytes: ~S is not a string" a
  | PBytesString, [a, b, c] => match a with
    | VBytes l => match b, c with
      | VFix s, VFix n =>
        if s < 0 || n < 0 || ((bytes_of m l).length : Int) < s + n
        then raise_v m "shen-jit.bytes->string: ~S is not a valid range" b
        else ret (VStr (((bytes_of m l).drop s.toNat).take n.toNat))
      | _, _ => raise_v m "shen-jit.bytes->string: ~S is not a valid range" b
    | _ => raise_v m "bytes: ~S is not a byte buffer" a
  | PCopyBytes, [a, b, c, e, n] => match a, c with
    | VBytes la, VBytes lc => match b, e, n with
      | VFix bi, VFix ei, VFix k =>
        if bi < 0 || ei < 0 || k < 0
           || (((bytes_of m la).length : Int) < bi + k || ((bytes_of m lc).length : Int) < ei + k)
        then raise_v m "shen-jit.copy-bytes: ~S is not a valid count" n
        else let src := ((bytes_of m lc).drop ei.toNat).take k.toNat
          ret_to (put_bytes m la (splice bi.toNat src (bytes_of m la))) d a
      | _, _, _ => raise_v m "shen-jit.copy-bytes: ~S is not a valid count" n
    | VBytes _, _ => raise_v m "bytes: ~S is not a byte buffer" c
    | _, _ => raise_v m "bytes: ~S is not a byte buffer" a
  | PBitNot, [a] => match a with | VFix x => ret (VFix (Z.lnot x)) | _ => raise_v m "bit operation: ~S is not an integer" a
  | PPopcount, [a] => match a with | VFix x => ret (VFix (popc 64 (word_of x))) | _ => raise_v m "bit operation: ~S is not an integer" a
  | PClz, [a] => match a with
    | VFix x => ret (VFix (if x == 0 then 62 else clz64 (word_of x)))
    | _ => raise_v m "bit operation: ~S is not an integer" a
  | PCtz, [a] => match a with
    | VFix x => ret (VFix (if x == 0 then 62 else ctz_go 64 (word_of x) 0 - 2))
    | _ => raise_v m "bit operation: ~S is not an integer" a
  | PBswap32, [a] => match a with
    | VFix x => if x < 0 || decide (4294967296 ≤ x) then raise_v m "shen-jit.bswap32: ~S does not fit in 32 bits" a
      else ret (VFix (le_read (le_bytes 4 x.toNat).reverse : Int))
    | _ => raise_v m "bit operation: ~S is not an integer" a
  | PBitAnd, [a, b] | PBitOr, [a, b] | PBitXor, [a, b] | PShiftLeft, [a, b] | PShiftRight, [a, b]
  | PRotate32, [a, b] => match a, b with
    | VFix x, VFix y => match p with
      | PBitAnd => ret (VFix (Z.land x y)) | PBitOr => ret (VFix (Z.lor x y)) | PBitXor => ret (VFix (Z.lxor x y))
      | _ =>
        if y < 0 || 63 < y then raise_v m "bit operation: ~S is not a valid shift" b else
        match p with
        | PShiftLeft => ret (VFix (of_word (u64 (Z.shiftl (word_of x) y))))
        | PShiftRight =>
          let s := if Z.testbit (word_of x) 63 then word_of x - 18446744073709551616 else word_of x
          ret (VFix (of_word (Z.land (u64 (Z.shiftr s y)) 18446744073709551612)))
        | _ =>
          if x < 0 || decide (4294967296 ≤ x) then raise_v m "shen-jit.rotate32: ~S does not fit in 32 bits" a else
          let k := Z.land y 31
          ret (VFix (Z.land (Z.lor (Z.shiftl x k) (Z.shiftr x (Z.land (32 - k) 31))) 4294967295))
    | VFix _, _ => raise_v m "bit operation: ~S is not an integer" b
    | _, _ => raise_v m "bit operation: ~S is not an integer" a
  | PDecimal, [s, e] => match s, e with
    | VStr x, VFix ex =>
      let (mant, own) := decimal_split x []
      ret (VReal (parse_decimal mant (ex + own)))
    | _, _ => raise_v m "shen-jit.decimal: ~S is not a string and an exponent" s
  | PPvar, [a] => match a with
    | VFix z => if z < 0 || 72057594037927935 < z then raise_v m "shen-jit.pvar: ~S is not a valid offset" a
      else ret (VPvar z)
    | _ => raise_v m "shen-jit.pvar: ~S is not a valid offset" a
  | PPvarp, [a] => isb (match a with | VPvar _ => true | _ => false)
  | PPvarOffset, [a] => match a with
    | VPvar z => ret (VFix z) | _ => raise_v m "shen-jit.pvar-offset: ~S is not a Prolog variable" a
  | PDeref, [a, b, mark] =>
    deref_go m d b mark ((match b with | VVec l => (vec_cells m l).length | _ => 0) + 1) a
  | PSamep, [a, b] => match same a b with | some r => isb r | none => MStuck RIdentity
  | PPointerp, [_] => isb false
  | PRaiseCond, [] => raise_s m "cond: no clause applies"
  | PGetTime, [a] => match a with
    | VSym s =>
      if s.eqb S_run then MIO (JTime true) (fun r => match r with
        | JTimeIs b => set_stack m (swrite m d (VReal b)) | _ => m)
      else if s.eqb S_unix then MIO (JTime false) (fun r => match r with
        | JTimeIs b => set_stack m (swrite m d (VReal b)) | _ => m)
      else raise_v m "get-time: ~S is not run or unix" a
    | _ => raise_v m "get-time: ~S is not run or unix" a
  | POpen, [path, dir] =>
    match path with
    | VStr ps =>
      let home := match tget S__home_directory_ m.m_gval with | some (VStr h) => h | _ => []
      let go ds := MIO (JOpen (home ++ ps) ds) (fun r => match r with
        | JOpened h => let (l, m') := alloc m (OStream h ds true); set_stack m' (swrite m' d (VStream l))
        | _ => match raise_v m "open: cannot open ~S" path with | MTau m' => m' | _ => m)
      match dir with
      | VSym s =>
        if s.eqb S_out then go SOut
        else if s.eqb S_in then go SIn
        else raise_v m "open: the direction ~S is not in or out" dir
      | _ => raise_v m "open: the direction ~S is not in or out" dir
    | _ => raise_v m "open: ~S is not a string" path
  | PClose, [s] => match s with
    | VStream l => match tget l m.m_heap with
      | some (OStream h dr true) =>
        let m1 := set_heap m (tset l (OStream h dr false) m.m_heap)
        MIO (JClose h) (fun r => match r with
          | JFailed => match raise_s m1 "close: the write failed" with | MTau m' => m' | _ => m1
          | _ => set_stack m1 (swrite m1 d VNil))
      | _ => ret VNil
    | _ => raise_v m "close: ~S is not a stream" s
  | PReadByte, [s] => match s with
    | VStream l => match tget l m.m_heap with
      | some (OStream h SIn true) => MIO (JRead h) (fun r => match r with
        | JByte b => set_stack m (swrite m d (VFix (b : Int)))
        | _ => set_stack m (swrite m d (VFix (-1))))
      | _ => raise_v m "read-byte: ~S is not an open input stream" s
    | _ => raise_v m "read-byte: ~S is not an open input stream" s
  | PWriteByte, [b, s] => match s with
    | VStream l => match tget l m.m_heap with
      | some (OStream h SOut true) => match b with
        | VFix z =>
          if decide (0 ≤ z) && decide (z ≤ 255)
          then MIO (JWrite h z.toNat) (fun r => match r with
            | JFailed => match raise_s m "write-byte: the write failed" with | MTau m' => m' | _ => m
            | _ => set_stack m (swrite m d b))
          else raise_v m "write-byte: ~S is not a byte" b
        | _ => raise_v m "write-byte: ~S is not a byte" b
      | _ => raise_v m "write-byte: ~S is not an open output stream" s
    | _ => raise_v m "write-byte: ~S is not an open output stream" s
  | PReadFile, [path, as_list] => match path with
    | VStr ps =>
      let home := match tget S__home_directory_ m.m_gval with | some (VStr h) => h | _ => []
      MIO (JReadFile (home ++ ps)) (fun r => match r with
        | JFile bs =>
          set_stack m (swrite m d (match as_list with
            | VBool true => of_list (bs.map (fun (b : Nat) => VFix (b : Int)))
            | _ => VStr bs))
        | _ => match raise_v m "open: cannot open ~S" path with | MTau m' => m' | _ => m)
    | _ => raise_v m "open: ~S is not a string" path
  | q, _ => if is_excluded q then MStuck (RExcluded q) else MStuck RArgs
where
  /-- deref's local `fix go`. -/
  deref_go (m : machine) (d : Nat) (b mark : val) : Nat → val → move
    | 0, _ => MStuck RCyclic
    | f + 1, x => match x with
      | VPvar off => match b with
        | VVec l => match (vec_cells m l)[off.toNat]? with
          | some bnd => match same bnd mark with
            | some true => ret_to m d x
            | some false => deref_go m d b mark f bnd
            | none => MStuck RIdentity
          | none => raise_v m "shen-jit.deref: ~S has no binding here" x
        | _ => raise_v m "shen-jit.deref: ~S has no binding here" x
      | _ => ret_to m d x

-- ---------- entering a procedure ----------
def enter (E : env) (m : machine) (callee : val) (count : Nat) (st : tree val) (fp : Nat) (ks : List cont) : move :=
  match callee with
  | VClo l => match tget l m.m_heap with
    | some (OClo c _) =>
      let m' := set_ctl m st fp c (code_ins c) ks
      let msg (_ : Unit) : text := match code_name c with
        | VSym s => text_of_sym s ++ t ": expected " ++ z_digits (code_arity c : Int)
                     ++ t (if code_arity c == 1 then " argument, got " else " arguments, got ")
                     ++ z_digits (count : Int)
        | _ => t "wrong number of arguments"
      let checked (r : List instr) :=
        if E.e_stack (fp + code_frame c) then raise_s m' "stack overflow" else MTau (set_rest m' r)
      if count == code_arity c then checked (code_ins c)
      else match code_entry c with
        | some (n, lb) =>
          if count == n then
            match find_label lb (code_ins c) with | some r => checked r | none => MStuck RBadLabel
          else raise m' (msg ()) VCleared
        | none => raise m' (msg ()) VCleared
    | _ => MStuck RBadCode
  | _ => MStuck RBadCode

def callee_named (m : machine) (f : Pos) : Sum val move :=
  match tget f m.m_gfun with
  | some (VClo l) => .inl (VClo l)
  | _ => .inr (raise_v m "undefined function ~S" (VSym f))
def callee_value (m : machine) (a : Nat) : Sum val move :=
  match sread m (a + 1) with
  | some (VClo l) => .inl (VClo l)
  | some VCleared | none => .inr (raise_v m "undefined function ~S" VCleared)
  | some v => .inr (raise_v m "~S is not a function" v)

def do_call (E : env) (m : machine) (d a n : Nat) (r : List instr) (cv : Sum val move) : move :=
  match cv with
  | .inr mv => mv
  | .inl callee =>
    let st := tset (skey (m.m_fp + a + 1)) callee m.m_stack
    enter E m callee n st (m.m_fp + a) (cont.Cont m.m_code r d a :: m.m_conts)

def move_args (st : tree val) (fp a : Nat) : Nat → Nat → Option (tree val)
  | 0, _ => some st
  | n + 1, i =>
    match tget (skey (fp + a + 2 + i)) st with
    | some v => move_args (tset (skey (fp + 2 + i)) v st) fp a n (i + 1)
    | none => none
def do_tail (E : env) (m : machine) (a n : Nat) (cv : Sum val move) : move :=
  match cv with
  | .inr mv => mv
  | .inl callee =>
    match (if a == 0 then some m.m_stack else move_args m.m_stack m.m_fp a n 0) with
    | some st => enter E m callee n (tset (skey (m.m_fp + 1)) callee st) m.m_fp m.m_conts
    | none => MStuck (RBadSlot a)

def read_op (m : machine) (o : operand) : Option val := match o with
  | OSlot s => sread m s
  | OConst k => (code_consts m.m_code)[k]?

def do_return (m : machine) (v : val) : move :=
  match m.m_conts with
  | [] => MFinal (FReturn v) m
  | k :: ks =>
    let fp := m.m_fp - k.k_window
    MTau (set_ctl m (tset (skey (fp + k.k_dst)) v m.m_stack) fp k.k_code k.k_rest ks)

-- ---------- one step ----------
def next (E : env) (ptab : tree (prim × Nat)) (m : machine) : move :=
  match m.m_rest with
  | [] => MStuck RFallOff
  | i :: r =>
    let m := set_rest m r
    match i with
    | IMove d s => match sread m s with
      | some v => MTau (set_stack m (swrite m d v)) | none => MStuck (RBadSlot s)
    | IConst d k => match (code_consts m.m_code)[k]? with
      | some v => MTau (set_stack m (swrite m d v)) | none => MStuck RBadConst
    | ICapture d c => match sread m 1 with
      | some (VClo l) => match tget l m.m_heap with
        | some (OClo _ caps) => match caps[c]? with
          | some v => MTau (set_stack m (swrite m d v)) | none => MStuck RBadCapture
        | _ => MStuck RBadCapture
      | _ => MStuck RBadCapture
    | IClosure d c ss =>
      match (code_codes m.m_code)[c]?, all_some (ss.map (sread m)) with
      | some nc, some caps =>
        if E.e_oom m.m_allocs then raise_s m "out of memory" else
        let (l, m') := alloc m (OClo nc caps); MTau (set_stack m' (swrite m' d (VClo l)))
      | none, _ => MStuck RBadCode
      | _, none => MStuck (RBadSlot d)
    | IPrim d p ops =>
      match all_some (ops.map (read_op m)) with
      | none => MStuck (RBadSlot d)
      | some args =>
        if allocates p && E.e_oom m.m_allocs then raise_s m "out of memory"
        else prim_step E ptab m d p args
    | ILabel _ | IInline _ _ | IEntry _ _ => MTau m
    | IJump l => match find_label l (code_ins m.m_code) with
      | some r' => MTau (set_rest m r') | none => MStuck RBadLabel
    | IJumpIfFalse o l => match read_op m o with
      | some (VBool true) => MTau m
      | some (VBool false) => match find_label l (code_ins m.m_code) with
        | some r' => MTau (set_rest m r') | none => MStuck RBadLabel
      | some v => raise_v m "~S is not a boolean" v
      | none => MStuck (RBadSlot 0)
    | ICall d a f n | ICallSealed d a f n => do_call E m d a n r (callee_named m f)
    | ICallValue d a n => do_call E m d a n r (callee_value m a)
    | ITail a f n | ITailSealed a f n => do_tail E m a n (callee_named m f)
    | ITailValue a n => do_tail E m a n (callee_value m a)
    | IReturn o => match read_op m o with
      | some v => do_return m v | none => MStuck (RBadSlot 0)
    | IPushHandler l =>
      match find_label l (code_ins m.m_code) with
      | none => MStuck RBadLabel
      | some after =>
        let quiet := match after with | IException _ :: _ => false | _ => true
        MTau (set_handlers m (handler.Handler m.m_code l m.m_fp m.m_conts quiet :: m.m_handlers))
    | IPopHandler => match m.m_handlers with
      | _ :: hs => MTau (set_handlers m hs) | [] => MStuck RBadCode
    | IException d => MTau (set_stack m (swrite m d m.m_exn))
    | IJumpUnlessEntry s n l =>
      let jump (_ : Unit) := match find_label l (code_ins m.m_code) with
        | some r' => MTau (set_rest m r') | none => MStuck RBadLabel
      match sread m s with
      | some (VClo c) => match tget c m.m_heap with
        | some (OClo cd _) => match code_entry cd with
          | some (x, _) => if x == n then MTau m else jump ()
          | none => jump ()
        | _ => jump ()
      | some _ => jump ()
      | none => MStuck (RBadSlot s)

-- ---------- running ----------
def boot_code : code := Code VNil 0 none 2 [] [IReturn (OConst 0)] [] VNil
def empty_machine : machine :=
  { m_stack := Leaf, m_fp := 0, m_code := boot_code, m_rest := [], m_conts := [],
    m_handlers := [], m_exn := VNil, m_heap := Leaf, m_next := Pos.one,
    m_gval := Leaf, m_gfun := Leaf, m_sealed := Leaf, m_seal_user := false, m_allocs := 0 }

inductive result | RDone (o : final) (m : machine) | RStuck (why : stuck) | RNeedsIO | ROutOfFuel

def run (E : env) (ptab : tree (prim × Nat)) : Nat → machine → result
  | 0, _ => .ROutOfFuel
  | f + 1, m => match next E ptab m with
    | MTau m' => run E ptab f m'
    | MIO _ _ => .RNeedsIO
    | MFinal o m' => .RDone o m'
    | MStuck w => .RStuck w

def start (E : env) (m : machine) (callee : val) : move :=
  let st := tset (skey 1) callee Leaf
  enter E (set_handlers m []) callee 0 st 0 []

end JitBytecode
