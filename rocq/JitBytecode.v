(* Shen/JIT Phase 1: an executable semantics of Shen/JIT's register bytecode, at
   pin 934cfa5 (0.6) (docs/bytecode.md, src/runtime/ops.h, loader.c, jit.c, prims.c,
   dict.c). This is a specification of the bytecode level. Nothing here relates
   it to the emitted machine code or to KLambda: those are open obligations in
   spec/obligations.json. `next` is a function, so one state has one move;
   JitMeta.v states what that gives. Where the implementation's behavior depends
   on something this model does not carry, the machine stops with a named stuck
   reason rather than guessing. *)
From Coq Require Import List ZArith NArith PArith Bool String Ascii.
From Buri Require Import JitFloat.
Import ListNotations.
Module JitBytecode.
Import JitFloat.JitFloat.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.

Definition text := list N.
Definition t (s : string) : text := map N_of_ascii (list_ascii_of_string s).

(* ---------- finite maps ---------- *)
Inductive tree (A : Type) := Leaf | Node (l : tree A) (v : option A) (r : tree A).
Arguments Leaf {A}. Arguments Node {A}.
Fixpoint tget {A} (k : positive) (m : tree A) : option A := match m with
 | Leaf => None
 | Node l v r => match k with xH => v | xO k => tget k l | xI k => tget k r end end.
Fixpoint tset {A} (k : positive) (x : A) (m : tree A) : tree A := match m with
 | Leaf => match k with
   | xH => Node Leaf (Some x) Leaf
   | xO k => Node (tset k x Leaf) None Leaf
   | xI k => Node Leaf None (tset k x Leaf) end
 | Node l v r => match k with
   | xH => Node l (Some x) r
   | xO k => Node (tset k x l) v r
   | xI k => Node l v (tset k x r) end end.

(* ---------- symbols: a name as one number, so a symbol is its name.
   src/runtime/objects.c interns by the name's bytes (memcmp), so two symbols are
   the same exactly when their names are. The number is a prefix code of the name,
   which is injective on every text, whatever its elements: each element n is
   written, lowest bit first, as the bits of n+1 below its leading 1, each behind
   a 1, then a 0. `text_of_sym` reads it back, and `text_of_sym_of_text` proves
   the round trip, so `sym_of_text` is injective (`sym_of_text_inj`).
   A collection can drop a symbol nothing reaches; re-interning makes a new one
   that nothing can tell from the old (docs/semantics.md section 2), which is why
   the model needs no intern table. ---------- *)
Fixpoint sym_push (q acc : positive) : positive := match q with
 | xH => xO acc
 | xO q => xI (xO (sym_push q acc))
 | xI q => xI (xI (sym_push q acc)) end.
Definition sym_of_text (s : text) : positive :=
 fold_right (fun n acc => sym_push (N.succ_pos n) acc) xH s.
Definition sym (s : string) : positive := sym_of_text (t s).
Definition S_move : positive := Eval vm_compute in sym "move".
Definition S_const : positive := Eval vm_compute in sym "const".
Definition S_capture : positive := Eval vm_compute in sym "capture".
Definition S_closure : positive := Eval vm_compute in sym "closure".
Definition S_prim : positive := Eval vm_compute in sym "prim".
Definition S_label : positive := Eval vm_compute in sym "label".
Definition S_jump : positive := Eval vm_compute in sym "jump".
Definition S_jump_if_false : positive := Eval vm_compute in sym "jump-if-false".
Definition S_call : positive := Eval vm_compute in sym "call".
Definition S_call_sealed : positive := Eval vm_compute in sym "call-sealed".
Definition S_call_value : positive := Eval vm_compute in sym "call-value".
Definition S_tail_call : positive := Eval vm_compute in sym "tail-call".
Definition S_tail_call_sealed : positive := Eval vm_compute in sym "tail-call-sealed".
Definition S_tail_call_value : positive := Eval vm_compute in sym "tail-call-value".
Definition S_return : positive := Eval vm_compute in sym "return".
Definition S_push_handler : positive := Eval vm_compute in sym "push-handler".
Definition S_pop_handler : positive := Eval vm_compute in sym "pop-handler".
Definition S_exception : positive := Eval vm_compute in sym "exception".
Definition S_entry : positive := Eval vm_compute in sym "entry".
Definition S_jump_unless_entry : positive := Eval vm_compute in sym "jump-unless-entry".
Definition S_inline : positive := Eval vm_compute in sym "inline".
Definition S_code : positive := Eval vm_compute in sym "code".
Definition S_defun : positive := Eval vm_compute in sym "defun".
Definition S_run : positive := Eval vm_compute in sym "run".
Definition S_unix : positive := Eval vm_compute in sym "unix".
Definition S_in : positive := Eval vm_compute in sym "in".
Definition S_out : positive := Eval vm_compute in sym "out".
Definition S_shen_fail_ : positive := Eval vm_compute in sym "shen.fail!".
Definition S__home_directory_ : positive := Eval vm_compute in sym "*home-directory*".
(* The name back from the number. `k` holds the bits of the element being read;
   a number no name gives (ending in 1 then the leading 1) reads as the name so far. *)
Fixpoint text_of_sym_go (p : positive) (k : positive -> positive) : text := match p with
 | xH => []
 | xO r => Pos.pred_N (k xH) :: text_of_sym_go r (fun x => x)
 | xI (xO r) => text_of_sym_go r (fun x => k (xO x))
 | xI (xI r) => text_of_sym_go r (fun x => k (xI x))
 | xI xH => [] end.
Definition text_of_sym (p : positive) : text := text_of_sym_go p (fun x => x).

Lemma text_of_sym_go_push : forall q acc k,
  text_of_sym_go (sym_push q acc) k = Pos.pred_N (k q) :: text_of_sym_go acc (fun x => x).
Proof.
 induction q as [q IH|q IH|]; intros acc k; simpl.
 - exact (IH acc (fun x => k (xI x))).
 - exact (IH acc (fun x => k (xO x))).
 - reflexivity.
Qed.

(* The round trip: every text is the name of its symbol. *)
Theorem text_of_sym_of_text : forall s, text_of_sym (sym_of_text s) = s.
Proof.
 induction s as [|n s IH]; [reflexivity|].
 unfold text_of_sym; simpl. rewrite text_of_sym_go_push.
 change (text_of_sym_go (sym_of_text s) (fun x => x)) with (text_of_sym (sym_of_text s)).
 rewrite IH. f_equal. destruct n as [|n]; [reflexivity|apply Pos.pred_N_succ].
Qed.

(* Distinct names are distinct symbols, for every text the KLambda spec admits. *)
Theorem sym_of_text_inj : forall s1 s2, sym_of_text s1 = sym_of_text s2 -> s1 = s2.
Proof.
 intros s1 s2 H. rewrite <- (text_of_sym_of_text s1), <- (text_of_sym_of_text s2), H. reflexivity.
Qed.

(* ---------- values, code, heap ---------- *)
Inductive val :=
 | VFix (z : Z) | VReal (bits : N) | VSym (s : positive) | VBool (b : bool) | VNil
 | VCleared                         (* unbound cell; never visible to Shen code *)
 | VStr (s : text) | VPair (a d : val)
 | VVec (l : positive) | VBytes (l : positive) | VClo (l : positive)
 | VExn (l : positive) | VStream (l : positive) | VPvar (off : Z).

Inductive prim :=
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
 | PCollect | PWriteBytes
 | PRaiseCond.

(* The primitive table in the order of primitive_table in prims.c. A gate compares
   these names and arities with the C source. *)
Local Open Scope nat_scope.
Definition prim_table : list (string * prim * nat) :=
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
 ;("shen-jit.collect",PCollect,0);("shen-jit.write-bytes",PWriteBytes,4)
 ;("raise-cond",PRaiseCond,0)].
Local Open Scope N_scope.

Inductive operand := OSlot (s : N) | OConst (k : N).
Inductive instr :=
 | IMove (d s : N) | IConst (d k : N) | ICapture (d i : N)
 | IClosure (d c : N) (ss : list N)
 | IPrim (d : N) (p : prim) (ops : list operand)
 | ILabel (l : N) | IJump (l : N) | IJumpIfFalse (o : operand) (l : N)
 | ICall (d a : N) (f : positive) (n : N) | ICallSealed (d a : N) (f : positive) (n : N)
 | ICallValue (d a n : N)
 | ITail (a : N) (f : positive) (n : N) | ITailSealed (a : N) (f : positive) (n : N)
 | ITailValue (a n : N)
 | IReturn (o : operand) | IPushHandler (l : N) | IPopHandler | IException (d : N)
 | IEntry (n l : N) | IJumpUnlessEntry (s n l : N) | IInline (f : positive) (n : N).

Inductive code := Code
 (c_name : val) (c_arity : N) (c_entry : option (N * N)) (c_frame : N)
 (c_consts : list val) (c_ins : list instr) (c_codes : list code) (c_inline : val).
Definition code_name c := match c with Code x _ _ _ _ _ _ _ => x end.
Definition code_arity c := match c with Code _ x _ _ _ _ _ _ => x end.
Definition code_entry c := match c with Code _ _ x _ _ _ _ _ => x end.
Definition code_frame c := match c with Code _ _ _ x _ _ _ _ => x end.
Definition code_consts c := match c with Code _ _ _ _ x _ _ _ => x end.
Definition code_ins c := match c with Code _ _ _ _ _ x _ _ => x end.
Definition code_codes c := match c with Code _ _ _ _ _ _ x _ => x end.
Definition code_inline c := match c with Code _ _ _ _ _ _ _ x => x end.

Inductive stream_dir := SIn | SOut.
Inductive obj :=
 | OVec (cells : list val) | OBytes (bs : list N)
 | OClo (c : code) (caps : list val)
 | OExn (msg : text) (v : val)      (* VCleared: no value beside the message *)
 | OStream (handle : N) (d : stream_dir) (is_open : bool).

Record cont := Cont { k_code : code; k_rest : list instr; k_dst : N; k_window : N }.
Record handler := Handler {
 h_code : code; h_label : N; h_fp : N; h_conts : list cont; h_quiet : bool }.

Record machine := Machine {
 m_stack : tree val; m_fp : N; m_code : code; m_rest : list instr;
 m_conts : list cont; m_handlers : list handler; m_exn : val;
 m_heap : tree obj; m_next : positive;
 m_gval : tree val; m_gfun : tree val; m_sealed : tree unit; m_seal_user : bool;
 m_allocs : N }.

(* The environment: what the bytecode level leaves to its surroundings. Each is a
   parameter, so a theorem about the machine holds for every choice of them.
   e_oom: which allocations a real run refuses (the collector's budget).
   e_stack: which frame tops raise "stack overflow".
   e_hash: XXH3_64bits of a byte string, as the runtime calls it. *)
Record env := Env { e_oom : N -> bool; e_stack : N -> bool; e_hash : text -> Z }.

Inductive jreq :=
 | JOpen (path : text) (d : stream_dir) | JClose (h : N)
 | JRead (h : N) | JWrite (h : N) (b : N) | JTime (run : bool) | JReadFile (path : text)
 | JWrites (h : N) (bs : list N).   (* 0.6: shen-jit.write-bytes, one fwrite of these bytes *)
Inductive jres :=
 | JOpened (h : N) | JFailed | JDone | JByte (b : N) | JEof | JTimeIs (bits : N) | JFile (bs : list N)
 | JReadFailed.   (* 0.6: a read error after a successful open (read-byte, shen-jit.read-file) *)

Inductive stuck :=
 | RBadSlot (s : N)           (* read of a slot never written: excluded by check.shen's rules *)
 | RBadConst | RBadLabel | RFallOff | RBadCapture | RBadCode
 | RIdentity                  (* the result depends on object identity, which the model omits *)
 | RCyclic                    (* = or hash through a cycle of absvectors *)
 | RExcluded (p : prim)       (* a primitive outside the named build *)
 | RArgs.                     (* a primitive given the wrong operand count: the loader rejects it *)

Inductive final := FReturn (v : val) | FError (e : val) | FExit (status : Z).
Inductive move :=
 | MTau (m : machine) | MIO (q : jreq) (k : jres -> machine)
 | MFinal (o : final) (m : machine) | MStuck (why : stuck).

(* ---------- small helpers ---------- *)
Definition skey (n : N) : positive := N.succ_pos n.
Definition sread (m : machine) (s : N) : option val := tget (skey (m_fp m + s)) (m_stack m).
Definition swrite (m : machine) (s : N) (v : val) : tree val := tset (skey (m_fp m + s)) v (m_stack m).
Definition set_stack (m : machine) (st : tree val) : machine :=
 {| m_stack := st; m_fp := m_fp m; m_code := m_code m; m_rest := m_rest m; m_conts := m_conts m;
    m_handlers := m_handlers m; m_exn := m_exn m; m_heap := m_heap m; m_next := m_next m;
    m_gval := m_gval m; m_gfun := m_gfun m; m_sealed := m_sealed m; m_seal_user := m_seal_user m;
    m_allocs := m_allocs m |}.
Definition set_rest (m : machine) (r : list instr) : machine :=
 {| m_stack := m_stack m; m_fp := m_fp m; m_code := m_code m; m_rest := r; m_conts := m_conts m;
    m_handlers := m_handlers m; m_exn := m_exn m; m_heap := m_heap m; m_next := m_next m;
    m_gval := m_gval m; m_gfun := m_gfun m; m_sealed := m_sealed m; m_seal_user := m_seal_user m;
    m_allocs := m_allocs m |}.
Definition set_ctl (m : machine) (st : tree val) (fp : N) (c : code) (r : list instr) (ks : list cont) : machine :=
 {| m_stack := st; m_fp := fp; m_code := c; m_rest := r; m_conts := ks;
    m_handlers := m_handlers m; m_exn := m_exn m; m_heap := m_heap m; m_next := m_next m;
    m_gval := m_gval m; m_gfun := m_gfun m; m_sealed := m_sealed m; m_seal_user := m_seal_user m;
    m_allocs := m_allocs m |}.
Definition set_handlers (m : machine) (hs : list handler) : machine :=
 {| m_stack := m_stack m; m_fp := m_fp m; m_code := m_code m; m_rest := m_rest m; m_conts := m_conts m;
    m_handlers := hs; m_exn := m_exn m; m_heap := m_heap m; m_next := m_next m;
    m_gval := m_gval m; m_gfun := m_gfun m; m_sealed := m_sealed m; m_seal_user := m_seal_user m;
    m_allocs := m_allocs m |}.
Definition set_exn (m : machine) (e : val) : machine :=
 {| m_stack := m_stack m; m_fp := m_fp m; m_code := m_code m; m_rest := m_rest m; m_conts := m_conts m;
    m_handlers := m_handlers m; m_exn := e; m_heap := m_heap m; m_next := m_next m;
    m_gval := m_gval m; m_gfun := m_gfun m; m_sealed := m_sealed m; m_seal_user := m_seal_user m;
    m_allocs := m_allocs m |}.
Definition set_heap (m : machine) (h : tree obj) : machine :=
 {| m_stack := m_stack m; m_fp := m_fp m; m_code := m_code m; m_rest := m_rest m; m_conts := m_conts m;
    m_handlers := m_handlers m; m_exn := m_exn m; m_heap := h; m_next := m_next m;
    m_gval := m_gval m; m_gfun := m_gfun m; m_sealed := m_sealed m; m_seal_user := m_seal_user m;
    m_allocs := m_allocs m |}.
Definition set_globals (m : machine) (gv gf : tree val) (se : tree unit) (su : bool) : machine :=
 {| m_stack := m_stack m; m_fp := m_fp m; m_code := m_code m; m_rest := m_rest m; m_conts := m_conts m;
    m_handlers := m_handlers m; m_exn := m_exn m; m_heap := m_heap m; m_next := m_next m;
    m_gval := gv; m_gfun := gf; m_sealed := se; m_seal_user := su; m_allocs := m_allocs m |}.
Definition alloc (m : machine) (o : obj) : positive * machine :=
 let l := m_next m in
 (l, {| m_stack := m_stack m; m_fp := m_fp m; m_code := m_code m; m_rest := m_rest m; m_conts := m_conts m;
        m_handlers := m_handlers m; m_exn := m_exn m; m_heap := tset l o (m_heap m);
        m_next := Pos.succ l; m_gval := m_gval m; m_gfun := m_gfun m; m_sealed := m_sealed m;
        m_seal_user := m_seal_user m; m_allocs := m_allocs m + 1 |}).

Fixpoint vlist (v : val) : option (list val) := match v with
 | VNil => Some [] | VPair a d => option_map (cons a) (vlist d) | _ => None end.
Fixpoint of_list (l : list val) : val := match l with [] => VNil | a :: d => VPair a (of_list d) end.

Definition fix_min : Z := - 2305843009213693952.
Definition fix_max : Z := 2305843009213693951.
Definition fix_fits (z : Z) : bool := (Z.leb fix_min z && Z.leb z fix_max)%bool.
Definition is_number (v : val) := match v with VFix _ | VReal _ => true | _ => false end.
Definition number (v : val) : N := match v with VFix z => of_Z z | VReal b => b | _ => 0 end.

(* compare_fix_real (prims.c): where a fixnum lies against a real, exactly, with no rounding of
   the integer. None for NaN. An infinity lies past every fixnum. *)
Definition compare_fix_real (i : Z) (b : N) : option comparison :=
 match classify b with
 | CNan => None
 | CInf neg => Some (if neg then Gt else Lt)
 | _ => match ratio b with
   | Some (neg, n, den) => Some (Z.compare (i * den) (if neg then - n else n))
   | None => None end end.

(* ---------- identity ---------- *)
(* Whether two values are one word. Immediates and objects with a location are
   exact. Pairs, strings and reals are heap objects whose identity this model does
   not track: two of one kind answer None. *)
Definition same (a b : val) : option bool := match a, b with
 | VFix x, VFix y => Some (Z.eqb x y) | VSym x, VSym y => Some (Pos.eqb x y)
 | VBool x, VBool y => Some (Bool.eqb x y) | VNil, VNil => Some true
 | VCleared, VCleared => Some true | VPvar x, VPvar y => Some (Z.eqb x y)
 | VVec x, VVec y | VBytes x, VBytes y | VClo x, VClo y | VExn x, VExn y | VStream x, VStream y =>
   Some (Pos.eqb x y)
 | VPair _ _, VPair _ _ | VStr _, VStr _ | VReal _, VReal _ => None
 | _, _ => Some false end.

Fixpoint text_eqb (a b : text) : bool := match a, b with
 | [], [] => true | x :: a, y :: b => (N.eqb x y && text_eqb a b)%bool | _, _ => false end.

Lemma text_eqb_true_iff : forall a b, text_eqb a b = true <-> a = b.
Proof.
 induction a as [|x a IH]; intros [|y b]; simpl; split; intro H; try discriminate; try reflexivity.
 - apply andb_true_iff in H as [H1 H2]. apply N.eqb_eq in H1. apply IH in H2. subst. reflexivity.
 - injection H as H1 H2. subst. apply andb_true_iff. split; [apply N.eqb_refl|apply IH; reflexivity].
Qed.

(* So the machine's symbol test is the source's name test (VR_sym). *)
Theorem sym_of_text_eqb : forall a b, Pos.eqb (sym_of_text a) (sym_of_text b) = text_eqb a b.
Proof.
 intros a b. destruct (text_eqb a b) eqn:E.
 - apply text_eqb_true_iff in E. subst. apply Pos.eqb_refl.
 - apply Pos.eqb_neq. intro H. apply sym_of_text_inj, text_eqb_true_iff in H. congruence.
Qed.

(* ---------- = (sj_equal) ---------- *)
Inductive eqr := EqT | EqF | EqIdentity | EqCycle.
Fixpoint eq_list (f : val -> val -> eqr) (xs ys : list val) : eqr := match xs, ys with
 | [], [] => EqT
 | x :: xs, y :: ys => match f x y with EqT => eq_list f xs ys | r => r end
 | _, _ => EqF end.
Fixpoint eq_val (h : tree obj) (fuel : nat) {struct fuel} : val -> val -> eqr :=
 match fuel with
 | O => fun _ _ => EqCycle
 | S f => fix go (a b : val) {struct a} : eqr :=
   match a, b with
   | VPair a1 a2, VPair b1 b2 => match go a1 b1 with EqT => go a2 b2 | r => r end
   | VFix x, VFix y => if Z.eqb x y then EqT else EqF
   | VFix x, VReal y => match compare_fix_real x y with Some Eq => EqT | _ => EqF end
   | VReal x, VFix y => match compare_fix_real y x with Some Eq => EqT | _ => EqF end
   | VReal x, VReal y =>
     (* C tests the two words first, so a NaN equals itself when it is the same
        object and nothing otherwise. The model does not track that. *)
     if (is_nan x && is_nan y)%bool then EqIdentity else if eqv x y then EqT else EqF
   | VStr x, VStr y => if text_eqb x y then EqT else EqF
   | VSym x, VSym y => if Pos.eqb x y then EqT else EqF
   | VBool x, VBool y => if Bool.eqb x y then EqT else EqF
   | VNil, VNil | VCleared, VCleared => EqT
   | VPvar x, VPvar y => if Z.eqb x y then EqT else EqF
   | VClo x, VClo y | VExn x, VExn y | VStream x, VStream y => if Pos.eqb x y then EqT else EqF
   | VVec x, VVec y =>
     if Pos.eqb x y then EqT else
     match tget x h, tget y h with
     | Some (OVec xs), Some (OVec ys) => eq_list (eq_val h f) xs ys
     | _, _ => EqCycle end
   | VBytes x, VBytes y =>
     if Pos.eqb x y then EqT else
     match tget x h, tget y h with
     | Some (OBytes xs), Some (OBytes ys) => if text_eqb xs ys then EqT else EqF
     | _, _ => EqCycle end
   | _, _ => EqF end end.
Definition eq_fuel : nat := 4096.

(* ---------- hash (hash_value, sj_hash) ---------- *)
Local Open Scope Z_scope.
Definition u64 (z : Z) : Z := Z.land z 18446744073709551615.
Definition mix (x : Z) : Z :=
 let x := Z.lxor x (Z.shiftr x 33) in
 let x := u64 (x * 18397679294719823053) in
 let x := Z.lxor x (Z.shiftr x 33) in
 let x := u64 (x * 14181476777654086739) in
 Z.lxor x (Z.shiftr x 33).
Definition special_word (n : Z) : Z := n * 8 + 2.
(* fuel bounds nesting; the budget of 256 bounds it first, so fuel cannot run out. *)
Fixpoint hash_go (E : env) (h : tree obj) (fuel : nat) (v : val) (budget : Z) {struct fuel} : Z * Z :=
 match fuel with O => (0, budget) | S f =>
 let budget := budget - 1 in
 if Z.ltb budget 0 then (0, budget) else
 match v with
 | VFix z => (mix (u64 z), budget)
 | VReal b =>
   match to_Z_exact b with
   | Some z => if Z.ltb (Z.abs z) 9200000000000000000 then (mix (u64 z), budget) else (mix (Z.of_N b), budget)
   | None => (mix (Z.of_N b), budget) end
 | VSym s => (e_hash E (text_of_sym s), budget)
 | VPair _ _ =>
   let fix walk (fl : nat) (x : val) (acc budget : Z) : Z * Z := match fl with
     | O => (acc, budget)
     | S fl => match x with
       | VPair a d =>
         if Z.leb budget 0 then let '(r, b) := hash_go E h f x budget in (mix (Z.lxor acc r), b)
         else let '(r, b) := hash_go E h f a budget in walk fl d (mix (Z.lxor acc r)) b
       | _ => let '(r, b) := hash_go E h f x budget in (mix (Z.lxor acc r), b) end end in
   walk 300%nat v 112 budget
 | VStr s => (e_hash E s, budget)
 | VBytes l => match tget l h with Some (OBytes bs) => (e_hash E bs, budget) | _ => (0, budget) end
 | VVec l => match tget l h with
   | Some (OVec cells) =>
     fold_left (fun st c => let '(acc, b) := st in
       if Z.leb b 0 then st else let '(r, b') := hash_go E h f c b in (mix (Z.lxor acc r), b'))
       cells (118, budget)
   | _ => (0, budget) end
 | VNil => (mix (special_word 0), budget)
 | VBool false => (mix (special_word 1), budget)
 | VBool true => (mix (special_word 2), budget)
 | VCleared => (mix (special_word 3), budget)
 | VPvar off => (mix (off * 256 + 250), budget)
 | VClo _ => (mix 80, budget)
 | VExn _ => (mix 10, budget)
 | VStream _ => (mix 9, budget)
 end end.
Definition sj_hash (E : env) (h : tree obj) (v : val) : Z := fst (hash_go E h 300 v 256).

Local Open Scope N_scope.
(* ---------- text of values ---------- *)
Definition fmt_real (b : N) : text := format_real b.
Definition to_string_atom (v : val) : text := match v with
 | VFix z => z_text z | VBool true => t "true" | VBool false => t "false" | VNil => t "()"
 | VPvar o => t "Var" ++ z_digits o | VSym s => text_of_sym s
 | VStr s => [34] ++ s ++ [34] | VReal b => fmt_real b
 | VPair _ _ => t "#<pair>" | VClo _ => t "#<procedure>" | VVec _ => t "#<absvector>"
 | VStream _ => t "#<stream>" | VBytes _ => t "#<bytes>" | VExn _ => t "#<exception>"
 | VCleared => t "#<value>" end.

(* show: error messages name the offending value in Shen notation. The 60-byte cut
   is applied to the result; the implementation stops walking there, which matters
   only for values too large or circular to walk, hence the fuel. *)
(* An absvector is <<...>> with all its elements; a vector, whose element 0 is a size
   that fits, is <1 2 3> with ... for an element not set. Items past the 60-byte cut
   cannot show, so only that many are walked. *)
Definition sep_join (items : list text) : text :=
 match items with [] => [] | x :: r => x ++ flat_map (fun i => [32] ++ i) r end.
Definition is_fail (v : val) : bool := match v with
 | VSym s => Pos.eqb s S_shen_fail_ | _ => false end.
Definition show_vec (sh : val -> text) (cells : list val) : text :=
 let cut l := firstn 61 l in
 match cells with
 | VFix z :: rest =>
   if andb (Z.leb 0 z) (Z.ltb z (Z.of_nat (List.length cells))) then
     t "<" ++ cut (sep_join (map (fun c => if is_fail c then t "..." else cut (sh c))
                             (firstn 61 (firstn (Z.to_nat z) rest)))) ++ t ">"
   else t "<<" ++ cut (sep_join (map (fun c => cut (sh c)) (firstn 61 cells))) ++ t ">>"
 | _ => t "<<" ++ cut (sep_join (map (fun c => cut (sh c)) (firstn 61 cells))) ++ t ">>" end.

Fixpoint show (h : tree obj) (fuel : nat) (v : val) {struct fuel} : text := match fuel with
 | O => [] | S f => match v with
 | VPair a d =>
   let fix tail (fl : nat) (x : val) : text := match fl with O => [] | S fl => match x with
     | VPair a d => t " " ++ show h f a ++ tail fl d
     | VNil => []
     | x => t " | " ++ show h f x end end in
   t "[" ++ show h f a ++ tail 64%nat d ++ t "]"
 | VVec l => match tget l h with
   | Some (OVec [VSym s; a; b]) =>
     if text_eqb (text_of_sym s) (t "shen.tuple")
     then t "(@p " ++ show h f a ++ t " " ++ show h f b ++ t ")"
     else show_vec (show h f) [VSym s; a; b]
   | Some (OVec cells) => show_vec (show h f) cells
   | _ => t "#<value>" end
 | VStr s => [34] ++ s ++ [34]
 | VNil => t "[]"
 | VClo _ => t "#<procedure>" | VStream _ => t "#<stream>" | VBytes _ => t "#<bytes>"
 | VExn _ => t "#<exception>" | VCleared => t "#<value>"
 | x => to_string_atom x end end.

Definition show_cut (h : tree obj) (v : val) : text :=
 let s := show h 64 v in
 if Nat.leb (List.length s) 60 then s else firstn 60 s ++ t "...".

(* Put the value where ~S stands in the message, or after the message. *)
Fixpoint subst_tilde (m rep : text) : option text := match m with
 | 126 :: 83 :: r => Some (rep ++ r)
 | c :: r => option_map (cons c) (subst_tilde r rep)
 | [] => None end.
Definition exception_text (h : tree obj) (msg : text) (v : val) : text := match v with
 | VCleared => msg
 | _ => let s := show_cut h v in
   match subst_tilde msg s with Some r => r | None => msg ++ [32] ++ s end end.

(* ---------- raising ---------- *)
Fixpoint find_label (l : N) (iss : list instr) : option (list instr) := match iss with
 | [] => None
 | ILabel x :: r => if N.eqb x l then Some r else find_label l r
 | _ :: r => find_label l r end.

Definition raise (m : machine) (msg : text) (v : val) : move :=
 match m_handlers m with
 | [] =>
   let '(l, m') := alloc m (OExn msg v) in MFinal (FError (VExn l)) m'
 | h :: hs =>
   match find_label (h_label h) (code_ins (h_code h)) with
   | None => MStuck RBadLabel
   | Some r =>
     if h_quiet h then
       MTau (set_exn (set_ctl (set_handlers m hs) (m_stack m) (h_fp h) (h_code h) r (h_conts h)) VNil)
     else
       let '(l, m') := alloc m (OExn msg v) in
       MTau (set_exn (set_ctl (set_handlers m' hs) (m_stack m') (h_fp h) (h_code h) r (h_conts h)) (VExn l))
   end end.
Definition raise_s (m : machine) (s : string) : move := raise m (t s) VCleared.
Definition raise_v (m : machine) (s : string) (v : val) : move := raise m (t s) v.

(* A primitive's result goes to the destination, and the code continues. *)
Definition ret_to (m : machine) (d : N) (v : val) : move := MTau (set_stack m (swrite m d v)).
Definition boolean (m : machine) (d : N) (b : bool) := ret_to m d (VBool b).

(* ---------- installing code (loader.c) ---------- *)
Inductive loaded (A : Type) := LOk (a : A) | LErr (msg : string).
Arguments LOk {A}. Arguments LErr {A}.
Definition small_int (v : val) (limit : Z) : option N := match v with
 | VFix z => if (Z.leb 0 z && Z.ltb z limit)%bool then Some (Z.to_N z) else None
 | _ => None end.
Definition lim (n : N) : Z := Z.of_N n.
Definition operand_of (v : val) (frame nconst : N) : option operand := match v with
 | VPair (VSym c) (VPair k VNil) =>
   if Pos.eqb c S_const then option_map OConst (small_int k (lim nconst)) else None
 | VPair _ _ => None
 | _ => option_map OSlot (small_int v (lim frame)) end.
Fixpoint all_some {A} (l : list (option A)) : option (list A) := match l with
 | [] => Some []
 | None :: _ => None
 | Some x :: r => option_map (cons x) (all_some r) end.
Fixpoint prim_lookup (s : positive) (l : list (string * prim * nat)) : option (prim * nat) := match l with
 | [] => None
 | (n, p, a) :: r => if Pos.eqb (sym n) s then Some (p, a) else prim_lookup s r end.

Definition b2 := 4294967295%Z.
Definition sn (v : val) (f : N) := small_int v (lim f).
Definition window_ok (a count frame : N) : bool := N.ltb (a + 1 + count) frame.

(* encode: operand kinds from `kinds` in loader.c. *)
Definition encode (ptab : tree (prim * nat)) (insn : val) (frame nconst ncode : N) : loaded instr :=
 match vlist insn with
 | None | Some [] => LErr "malformed instruction"
 | Some (VSym op :: args) =>
   let bad := LErr "bad operand" in
   let cnt := LErr "wrong operand count" in
   let win := LErr "call window outside the frame" in
   let iss s := Pos.eqb op (sym s) in
   if iss "move" then match args with
     | [d; s] => match sn d frame, sn s frame with Some d, Some s => LOk (IMove d s) | _, _ => bad end
     | _ => cnt end
   else if iss "const" then match args with
     | [d; k] => match sn d frame, sn k nconst with Some d, Some k => LOk (IConst d k) | _, _ => bad end
     | _ => cnt end
   else if iss "capture" then match args with
     | [d; i] => match sn d frame, small_int i 256 with Some d, Some i => LOk (ICapture d i) | _, _ => bad end
     | _ => cnt end
   else if iss "closure" then match args with
     | d :: c :: ss => match sn d frame, sn c ncode, all_some (map (fun s => sn s frame) ss) with
       | Some d, Some c, Some ss => LOk (IClosure d c ss) | _, _, _ => bad end
     | _ => cnt end
   else if iss "prim" then match args with
     | d :: VSym p :: os =>
       match sn d frame with None => bad | Some d =>
       match tget p ptab with
       | Some (pr, a) =>
         if Nat.eqb a (List.length os) then
           match all_some (map (fun o => operand_of o frame nconst) os) with
           | Some os => LOk (IPrim d pr os) | None => bad end
         else LErr "unknown primitive or wrong arity"
       | None => LErr "unknown primitive or wrong arity" end end
     | _ :: _ :: _ => LErr "unknown primitive or wrong arity"
     | _ => cnt end
   else if iss "label" then match args with
     | [l] => match small_int l b2 with Some l => LOk (ILabel l) | None => bad end | _ => cnt end
   else if iss "jump" then match args with
     | [l] => match small_int l b2 with Some l => LOk (IJump l) | None => bad end | _ => cnt end
   else if iss "jump-if-false" then match args with
     | [o; l] => match operand_of o frame nconst, small_int l b2 with
       | Some o, Some l => LOk (IJumpIfFalse o l) | _, _ => bad end
     | _ => cnt end
   else if orb (iss "call") (iss "call-sealed") then match args with
     | [d; a; VSym f; n] => match sn d frame, sn a frame, small_int n 256 with
       | Some d, Some a, Some n =>
         if window_ok a n frame then LOk (if iss "call" then ICall d a f n else ICallSealed d a f n) else win
       | _, _, _ => bad end
     | [_; _; _; _] => bad
     | _ => cnt end
   else if iss "call-value" then match args with
     | [d; a; n] => match sn d frame, sn a frame, small_int n 256 with
       | Some d, Some a, Some n => if window_ok a n frame then LOk (ICallValue d a n) else win
       | _, _, _ => bad end
     | _ => cnt end
   else if orb (iss "tail-call") (iss "tail-call-sealed") then match args with
     | [a; VSym f; n] => match sn a frame, small_int n 256 with
       | Some a, Some n =>
         if window_ok a n frame then LOk (if iss "tail-call" then ITail a f n else ITailSealed a f n) else win
       | _, _ => bad end
     | [_; _; _] => bad
     | _ => cnt end
   else if iss "tail-call-value" then match args with
     | [a; n] => match sn a frame, small_int n 256 with
       | Some a, Some n => if window_ok a n frame then LOk (ITailValue a n) else win
       | _, _ => bad end
     | _ => cnt end
   else if iss "return" then match args with
     | [o] => match operand_of o frame nconst with Some o => LOk (IReturn o) | None => bad end | _ => cnt end
   else if iss "push-handler" then match args with
     | [l] => match small_int l b2 with Some l => LOk (IPushHandler l) | None => bad end | _ => cnt end
   else if iss "pop-handler" then match args with [] => LOk IPopHandler | _ => cnt end
   else if iss "exception" then match args with
     | [d] => match sn d frame with Some d => LOk (IException d) | None => bad end | _ => cnt end
   else if iss "entry" then match args with
     | [n; l] => match small_int n 256, small_int l b2 with
       | Some n, Some l => LOk (IEntry n l) | _, _ => bad end
     | _ => cnt end
   else if iss "jump-unless-entry" then match args with
     | [s; n; l] => match sn s frame, small_int n 256, small_int l b2 with
       | Some s, Some n, Some l => LOk (IJumpUnlessEntry s n l) | _, _, _ => bad end
     | _ => cnt end
   else if iss "inline" then match args with
     | [VSym f; n] => match small_int n b2 with Some n => LOk (IInline f n) | None => bad end
     | [_; _] => bad
     | _ => cnt end
   else LErr "unknown instruction"
 | Some _ => LErr "unknown instruction" end.

(* The instructions of code written by hand (real and word registers, loops): outside the named
   build. A gate compares this list with ops.h. The lowerer does not emit them, and the model refuses
   them when loading, where the real loader accepts them. *)
Definition excluded_ops : list string :=
 ["loop";"again";"real-number";"real-box";"real-move";"real-neg";"real-abs";"real-sqrt";"real+";"real-";"real*";"real/"
 ;"real-unless<";"real-unless>";"real-unless<=";"real-unless>=";"real-unless=";"real-load";"real-store"
 ;"real-load-at";"real-store-at";"real-from-word";"word-from-real";"word-number";"word-box";"word-move"
 ;"word+";"word-";"word*";"word-and";"word-or";"word-xor";"word-shl";"word-shr";"word-sar";"word-rotl";"word-rotr"
 ;"word-unless<";"word-unless>";"word-unless<=";"word-unless>=";"word-unless=";"word-unless-u<";"word-unless-u>"
 ;"word-unless-u<=";"word-unless-u>=";"word-load8";"word-load16";"word-load32";"word-load-s32";"word-load64"
 ;"word-store8";"word-store16";"word-store32";"word-store64"]%string.

(* check_control: labels defined once, targets defined, entry first, ends in a transfer. *)
Definition target_of (i : instr) : option N := match i with
 | IJump l | IPushHandler l | IJumpIfFalse _ l | IEntry _ l | IJumpUnlessEntry _ _ l => Some l
 | _ => None end.
Fixpoint labels_of (iss : list instr) : list N := match iss with
 | [] => [] | ILabel l :: r => l :: labels_of r | _ :: r => labels_of r end.
Fixpoint nodup_N (l : list N) : bool := match l with
 | [] => true | x :: r => (negb (existsb (N.eqb x) r) && nodup_N r)%bool end.
Definition is_entry (i : instr) := match i with IEntry _ _ => true | _ => false end.
Definition is_transfer (i : instr) := match i with
 | IReturn _ | IJump _ | ITail _ _ _ | ITailSealed _ _ _ | ITailValue _ _ => true | _ => false end.
Definition check_control (iss : list instr) : bool :=
 match iss with [] => false | first :: rest =>
   let ls := labels_of iss in
   (nodup_N ls
    && forallb (fun i => match target_of i with
                 | Some l => existsb (N.eqb l) ls | None => true end) iss
    && negb (existsb is_entry rest)
    && is_transfer (last iss first))%bool end.

Fixpoint map_loaded {A B} (f : A -> loaded B) (l : list A) : loaded (list B) := match l with
 | [] => LOk []
 | x :: r => match f x with
   | LErr e => LErr e
   | LOk y => match map_loaded f r with LErr e => LErr e | LOk ys => LOk (y :: ys) end end end.

Fixpoint build_code (ptab : tree (prim * nat)) (fuel : nat) (form : val) : loaded code :=
 match fuel with O => LErr "malformed code object" | S f =>
 match vlist form with
 | Some (VSym hd :: name :: arity :: frame :: consts :: insns :: codes :: more) =>
   if negb (Pos.eqb hd S_code) then LErr "malformed code object" else
   match more, small_int arity 256, small_int frame 1048576, vlist consts, vlist insns, vlist codes with
   | ([] | [_]), Some ar, Some fr, Some cs, Some iss, Some ns =>
     if N.ltb fr (ar + 2) then LErr "malformed code object" else
     let inl := match more with [x] => x | _ => VNil end in
     match map_loaded (build_code ptab f) ns with
     | LErr e => LErr e
     | LOk nested =>
       match map_loaded (fun i => encode ptab i fr (N.of_nat (List.length cs)) (N.of_nat (List.length ns))) iss with
       | LErr e => LErr e
       | LOk ins =>
         if negb (check_control ins) then LErr "bad control flow: labels or the final instruction" else
         match ins with
         | IEntry n l :: _ =>
           if orb (N.leb n ar) (N.ltb fr (n + 2))
           then LErr "entry outside the frame or not above the arity"
           else LOk (Code name ar (Some (n, l)) fr cs ins nested inl)
         | _ => LOk (Code name ar None fr cs ins nested inl) end end end
   | _, _, _, _, _, _ => LErr "malformed code object" end
 | _ => LErr "malformed code object" end end.

Definition prim_tree : tree (prim * nat) :=
 fold_left (fun tr e => let '(n, p, a) := e in tset (sym n) (p, a) tr) prim_table Leaf.

(* The install primitive. d is where the result goes. *)
Definition install (ptab : tree (prim * nat)) (m : machine) (d : N) (form : val) : move :=
 let build c :=
   match build_code ptab 64 c with
   | LErr e => inl e
   | LOk code => inr (alloc m (OClo code [])) end in
 match vlist form with
 | Some [VSym h; VSym name; c] =>
   if Pos.eqb h S_defun then
     match tget name (m_sealed m) with
     | Some _ => raise_v m "~S is sealed and cannot be redefined" (VSym name)
     | None =>
       match build c with
       | inl e => raise_s m e
       | inr (l, m') =>
         let se := if m_seal_user m' then tset name tt (m_sealed m') else m_sealed m' in
         let m'' := set_globals m' (m_gval m') (tset name (VClo l) (m_gfun m')) se (m_seal_user m') in
         ret_to m'' d (VSym name) end end
   else raise_s m "install: expected (defun Name Code) or a code object"
 | _ =>
   match form with
   | VPair (VSym h) _ =>
     if Pos.eqb h S_code then
       match build form with
       | inl e => raise_s m e
       | inr (l, m') => ret_to m' d (VClo l) end
     else raise_s m "install: expected (defun Name Code) or a code object"
   | _ => raise_s m "install: expected (defun Name Code) or a code object" end end.

(* ---------- primitives ---------- *)
Definition symbol_char (c : N) : bool :=
 ((N.leb 97 c && N.leb c 122) || (N.leb 65 c && N.leb c 90) || (N.leb 48 c && N.leb c 57)
  || existsb (N.eqb c) (t "=-*/+_?$!@~.><&%'#`"))%bool.
Definition name_kind (s : text) : Z := match s with
 | [c] => if existsb (N.eqb c) (t "{}:;,") then 1%Z
          else if (N.leb 48 c && N.leb c 57)%bool then 0%Z
          else if symbol_char c then (if (N.leb 65 c && N.leb c 90)%bool then 2%Z else 1%Z) else 0%Z
 | [] => 0%Z
 | c :: _ =>
   if (N.leb 48 c && N.leb c 57)%bool then 0%Z
   else if forallb symbol_char s then (if (N.leb 65 c && N.leb c 90)%bool then 2%Z else 1%Z) else 0%Z end.

Fixpoint replace {A} (n : nat) (x : A) (l : list A) : list A := match n, l with
 | O, _ :: r => x :: r | S n, y :: r => y :: replace n x r | _, [] => [] end.

(* Bytes as little-endian numbers. *)
Fixpoint le_read (bs : list N) : N := match bs with [] => 0 | b :: r => b + 256 * le_read r end.
Fixpoint le_bytes (w : nat) (x : N) : list N := match w with
 | O => [] | S w => N.land x 255 :: le_bytes w (N.shiftr x 8) end.
Definition splice {A} (at_ : nat) (src dst : list A) : list A :=
 firstn at_ dst ++ src ++ skipn (at_ + List.length src) dst.

(* A fixnum's word is its value shifted left by two, in 64 bits. *)
Definition word_of (z : Z) : Z := u64 (z * 4).
Definition of_word (w : Z) : Z :=
 let s := if Z.testbit w 63 then (w - 18446744073709551616)%Z else w in Z.div s 4.
Fixpoint popc (fuel : nat) (w : Z) : Z := match fuel with
 | O => 0%Z | S f => if Z.eqb w 0 then 0%Z else (Z.land w 1 + popc f (Z.shiftr w 1))%Z end.
Definition clz64 (w : Z) : Z := (63 - Z.log2 w)%Z.
Fixpoint ctz_go (fuel : nat) (w : Z) (n : Z) : Z := match fuel with
 | O => n | S f => if Z.testbit w 0 then n else ctz_go f (Z.shiftr w 1) (n + 1) end.

Definition vec_cells (m : machine) (l : positive) : list val :=
 match tget l (m_heap m) with Some (OVec c) => c | _ => [] end.
Definition put_vec (m : machine) (l : positive) (c : list val) : machine :=
 set_heap m (tset l (OVec c) (m_heap m)).

(* ---------- dictionaries (dict.c), a dictionary being a vector [tag count buckets].
   An entry is replaced rather than changed in place: a program holding an entry
   from dict-find across dict-put could tell (ledger: OB-JIT-DICT-ALIAS). ---------- *)
Definition dict_parts (m : machine) (d : val) : option (positive * val * Z * positive * list val) :=
 match d with
 | VVec l => match vec_cells m l with
   | [tag; VFix n; VVec b] =>
     if Z.ltb n 0 then None else
     let bs := vec_cells m b in
     let len := N.of_nat (List.length bs) in
     (* a nonzero power of two *)
     if andb (N.ltb 0 len) (N.eqb (N.land len (len - 1)) 0)
     then Some (l, tag, n, b, bs) else None
   | _ => None end
 | _ => None end.
Definition bucket_index (E : env) (m : machine) (k : val) (len : nat) : nat :=
 Z.to_nat (Z.land (sj_hash E (m_heap m) k) (Z.of_nat len - 1)).
Fixpoint bucket_find (h : tree obj) (k : val) (c : val) : option (option (val * val)) := match c with
 | VNil => Some None
 | VPair (VPair kk vv) r =>
   match eq_val h eq_fuel kk k with
   | EqT => Some (Some (kk, vv))
   | EqF => bucket_find h k r
   | _ => None end
 | _ => None end.

(* n->string from 0.6 (prims.c P_N_STRING): 0 to 255 as one byte, as the reader passes source bytes
   through it; any other Unicode scalar value as its UTF-8 bytes; anything else None, which raises. *)
Definition utf8_of (z : Z) : option (list N) :=
 if orb (Z.ltb z 0) (orb (Z.ltb 1114111 z) (andb (Z.leb 55296 z) (Z.leb z 57343))) then None
 else if Z.leb z 255 then Some [Z.to_N z]
 else if Z.leb z 2047 then
   Some [Z.to_N (192 + Z.shiftr z 6); Z.to_N (128 + Z.land z 63)]
 else if Z.leb z 65535 then
   Some [Z.to_N (224 + Z.shiftr z 12); Z.to_N (128 + Z.land (Z.shiftr z 6) 63); Z.to_N (128 + Z.land z 63)]
 else
   Some [Z.to_N (240 + Z.shiftr z 18); Z.to_N (128 + Z.land (Z.shiftr z 12) 63);
         Z.to_N (128 + Z.land (Z.shiftr z 6) 63); Z.to_N (128 + Z.land z 63)].

Definition bytes_of (m : machine) (l : positive) : list N :=
 match tget l (m_heap m) with Some (OBytes b) => b | _ => [] end.
Definition put_bytes (m : machine) (l : positive) (b : list N) : machine :=
 set_heap m (tset l (OBytes b) (m_heap m)).

Definition allocates (p : prim) : bool := match p with
 | PAdd | PSub | PMul | PDiv | PCons | PCn | PTlstr | PStr | PAbsvector | PFilledVector | PAbsvector3
 | PAppend | PBytesNew | PStringBytes | PBytesString | PDictPut | PDictEntries | PDecimal | PPos | PNString
 | PGetTime | POpen | PReadFile => true
 | _ => false end.

Definition is_excluded (p : prim) : bool := match p with
 | PMarkToplevel | PTraceText | PBacktrace | PSaveExecutable | PThread | PForeign
 | PPointerKind | PPointerAddress | PBytesPointer | PPointerString | PPointerBytes | PErrno | PCErrno
 | PPointerKill
 | PS32 | PS64 | PF32 | PF64 | PSetS32 | PSetS64 | PSetF32 | PSetF64
 | PPointerSized | PSetPointer | PPointerGuard | PPointerOwner | PPointersDead | PPointerReadOnly => true
 | _ => false end.

Definition prim_step (E : env) (ptab : tree (prim * nat)) (m : machine) (d : N) (p : prim) (args : list val) : move :=
 let ret := ret_to m d in
 let isb := boolean m d in
 match p, args with
 | (PAdd | PSub | PMul | PDiv), [a; b] =>
   if negb (is_number a) then raise_v m "~S is not a number" a
   else if negb (is_number b) then raise_v m "~S is not a number" b
   else if match p, b with
        | PDiv, VFix z => Z.eqb z 0 | PDiv, VReal r => is_zero r | _, _ => false end
   then raise_s m "division by zero"
   else match a, b with
   | VFix x, VFix y =>
     match p with
     | PDiv =>
       if negb (Z.eqb (Z.rem x y) 0) then ret (VReal (div (of_Z x) (of_Z y)))
       else let r := Z.quot x y in if fix_fits r then ret (VFix r) else raise_s m "integer overflow"
     | _ =>
       let r := match p with PAdd => (x + y)%Z | PSub => (x - y)%Z | _ => (x * y)%Z end in
       if fix_fits r then ret (VFix r) else raise_s m "integer overflow" end
   | _, _ =>
     let x := number a in let y := number b in
     ret (VReal (match p with PAdd => add x y | PSub => sub x y | PMul => mul x y | _ => div x y end)) end
 | (PLt | PGt | PLe | PGe), [a; b] =>
   if negb (is_number a) then raise_v m "~S is not a number" a
   else if negb (is_number b) then raise_v m "~S is not a number" b
   else match a, b with
   | VFix x, VFix y => isb (match p with
       | PLt => Z.ltb x y | PGt => Z.gtb x y | PLe => Z.leb x y | _ => Z.geb x y end)
   | VFix x, VReal r => isb (match compare_fix_real x r, p with
       | Some Lt, (PLt | PLe) | Some Gt, (PGt | PGe) | Some Eq, (PLe | PGe) => true | _, _ => false end)
   | VReal r, VFix y => isb (match compare_fix_real y r, p with
       | Some Gt, (PLt | PLe) | Some Lt, (PGt | PGe) | Some Eq, (PLe | PGe) => true | _, _ => false end)
   | _, _ =>
     let x := number a in let y := number b in
     isb (match p with PLt => lt x y | PGt => gt x y | PLe => le x y | _ => ge x y end) end
 | PEq, [a; b] => match eq_val (m_heap m) eq_fuel a b with
   | EqT => isb true | EqF => isb false
   | EqIdentity => MStuck RIdentity | EqCycle => MStuck RCyclic end
 | PNumberp, [a] => isb (is_number a)
 | PCollect, [] => isb true
 | PCons, [a; b] => ret (VPair a b)
 | PHd, [v] => match v with VPair a _ => ret a | _ => raise_v m "hd: ~S is not a pair" v end
 | PTl, [v] => match v with VPair _ b => ret b | _ => raise_v m "tl: ~S is not a pair" v end
 | PConsp, [v] => isb (match v with VPair _ _ => true | _ => false end)
 | PStringp, [v] => isb (match v with VStr _ => true | _ => false end)
 | PAbsvector, [v] => match v with
   | VFix n => if (Z.ltb n 0 || Z.leb 281474976710656 n)%bool then raise_v m "absvector: ~S is not a valid length" v else
     let '(l, m') := alloc m (OVec (repeat (VSym S_shen_fail_) (Z.to_nat n))) in ret_to m' d (VVec l)
   | _ => raise_v m "absvector: ~S is not a valid length" v end
 | PAbsvectorp, [v] => isb (match v with VVec _ => true | _ => false end)
 | PGetAddress, [v; i] => match v with
   | VVec l => match i with
     | VFix z => if Z.ltb z 0 then raise_v m "<-address: ~S is not a valid index" i else
       match nth_error (vec_cells m l) (Z.to_nat z) with
       | Some x => ret x | None => raise_v m "<-address: ~S is not a valid index" i end
     | _ => raise_v m "<-address: ~S is not a valid index" i end
   | _ => raise_v m "<-address: ~S is not an absvector" v end
 | PSetAddress, [v; i; x] => match v with
   | VVec l => match i with
     | VFix z =>
       if orb (Z.ltb z 0) (Nat.leb (List.length (vec_cells m l)) (Z.to_nat z))
       then raise_v m "address->: ~S is not a valid index" i
       else ret_to (put_vec m l (replace (Z.to_nat z) x (vec_cells m l))) d v
     | _ => raise_v m "address->: ~S is not a valid index" i end
   | _ => raise_v m "address->: ~S is not an absvector" v end
 | PSet, [a; b] => match a with
   | VSym s => ret_to (set_globals m (tset s b (m_gval m)) (m_gfun m) (m_sealed m) (m_seal_user m)) d b
   | _ => raise_v m "set: ~S is not a symbol" a end
 | PValue, [a] => match a with
   | VSym s => match tget s (m_gval m) with
     | Some VCleared | None => raise_v m "~S has no value" a
     | Some v => ret v end
   | _ => raise_v m "value: ~S is not a symbol" a end
 | PSimpleError, [a] => match a with
   | VStr s => raise m s VCleared
   | _ => raise_v m "simple-error: ~S is not a string" a end
 | PErrorToString, [a] => match a with
   | VExn l => match tget l (m_heap m) with
     | Some (OExn msg v) => ret (VStr (exception_text (m_heap m) msg v))
     | _ => MStuck RBadCode end
   | _ => raise_v m "error-to-string: ~S is not an exception" a end
 | PCn, [a; b] => match a, b with
   | VStr x, VStr y => ret (VStr (x ++ y))
   | VStr _, _ => raise_v m "cn: ~S is not a string" b
   | _, _ => raise_v m "cn: ~S is not a string" a end
 | PPos, [a; b] => match a with
   | VStr s => match b with
     | VFix z => if Z.ltb z 0 then raise_v m "pos: ~S is not a valid index" b else
       match nth_error s (Z.to_nat z) with
       | Some c => ret (VStr [c]) | None => raise_v m "pos: ~S is not a valid index" b end
     | _ => raise_v m "pos: ~S is not a valid index" b end
   | _ => raise_v m "pos: ~S is not a string" a end
 | PTlstr, [a] => match a with
   | VStr (_ :: r) => ret (VStr r)
   | _ => raise_v m "tlstr: ~S is not a non-empty string" a end
 | PStr, [a] => ret (VStr (to_string_atom a))
 | PNString, [a] => match a with
   | VFix z => match utf8_of z with
     | Some bs => ret (VStr bs)
     | None => raise_v m "n->string: ~S is not a byte or a Unicode scalar value" a end
   | _ => raise_v m "n->string: ~S is not a byte or a Unicode scalar value" a end
 | PStringN, [a] => match a with
   | VStr (c :: _) => ret (VFix (Z.of_N c))
   | _ => raise_v m "string->n: ~S is not a non-empty string" a end
 | PIntern, [a] => match a with
   | VStr s => if text_eqb s (t "true") then ret (VBool true)
               else if text_eqb s (t "false") then ret (VBool false)
               else ret (VSym (sym_of_text s))
   | _ => raise_v m "intern: ~S is not a string" a end
 | PEvalKl, [_] => raise_s m "eval-kl is lowered as a call to shen-jit.eval-kl"
 | PCharStreamp, [_] => isb false
 | PReadUnitString, [_] | PWriteString, [_; _] => raise_s m "character streams are not supported"
 | PInstall, [form] => install ptab m d form
 | PSymbolp, [a] => isb (match a with VSym _ => true | _ => false end)
 | PHash, [a; b] => match b with
   | VFix n => if Z.leb n 0 then raise_v m "hash: ~S is not a valid bound" b else
     let h := Z.rem (sj_hash E (m_heap m) a) n in ret (VFix (if Z.eqb h 0 then 1 else h))
   | _ => raise_v m "hash: ~S is not a valid bound" b end
 | PExit, [a] => match a with
   | VFix z => if (Z.leb 0 z && Z.leb z 255)%bool then MFinal (FExit z) m
               else raise_v m "~S is not an exit status" a
   | _ => raise_v m "~S is not an exit status" a end
 | PSymbolKind, [a] => ret (VFix (match a with VSym s => name_kind (text_of_sym s) | _ => 0 end))
 | PFilledVector, [a; x] => match a with
   | VFix n => if (Z.ltb n 0 || Z.leb 281474976710656 n)%bool then raise_v m "shen-jit.filled-vector: ~S is not a valid length" a else
     let '(l, m') := alloc m (OVec (repeat x (Z.to_nat n))) in ret_to m' d (VVec l)
   | _ => raise_v m "shen-jit.filled-vector: ~S is not a valid length" a end
 | PDictFind, [dv; k] => match dict_parts m dv with
   | None => raise_v m "~S is not a dictionary" dv
   | Some (_, _, _, _, bs) =>
     match nth_error bs (bucket_index E m k (List.length bs)) with
     | Some c => match bucket_find (m_heap m) k c with
       | Some (Some (kk, vv)) => ret (VPair kk vv)
       | Some None => ret VNil
       | None => raise_v m "~S is not a dictionary" dv end
     | None => raise_v m "~S is not a dictionary" dv end end
 | PDictPut, [dv; k; v] => match dict_parts m dv with
   | None => raise_v m "~S is not a dictionary" dv
   | Some (l, tag, n, b, bs) =>
     let i := bucket_index E m k (List.length bs) in
     let c := match nth_error bs i with Some c => c | None => VNil end in
     let fix put_in (c : val) : val := match c with
       | VPair (VPair kk vv) r =>
         match eq_val (m_heap m) eq_fuel kk k with
         | EqT => VPair (VPair kk v) r | _ => VPair (VPair kk vv) (put_in r) end
       | x => x end in
     match bucket_find (m_heap m) k c with
     | None => raise_v m "~S is not a dictionary" dv
     | Some (Some _) => ret_to (put_vec m b (replace i (put_in c) bs)) d v
     | Some None =>
       let bs' := replace i (VPair (VPair k v) c) bs in
       let m1 := put_vec m b bs' in
       let n' := (n + 1)%Z in
       if Z.ltb (Z.of_nat (List.length bs)) n' then
         (* grow: double, relinking each bucket from its head (dict.c, grow) *)
         let len := (2 * List.length bs)%nat in
         let fresh := fold_left (fun acc cell_list =>
           let fix go (cl : val) (acc : list val) : list val := match cl with
             | VPair (VPair kk vv) r =>
               let j := bucket_index E m kk len in
               let cur := match nth_error acc j with Some x => x | None => VNil end in
               go r (replace j (VPair (VPair kk vv) cur) acc)
             | _ => acc end in
           go cell_list acc) (vec_cells m1 b) (repeat VNil len) in
         let '(nb, m2) := alloc m1 (OVec fresh) in
         ret_to (put_vec m2 l [tag; VFix n'; VVec nb]) d v
       else ret_to (put_vec m1 l [tag; VFix n'; VVec b]) d v end end
 | PDictRemove, [dv; k] => match dict_parts m dv with
   | None => raise_v m "~S is not a dictionary" dv
   | Some (l, tag, n, b, bs) =>
     let i := bucket_index E m k (List.length bs) in
     let c := match nth_error bs i with Some c => c | None => VNil end in
     let fix rm (c : val) : val := match c with
       | VPair (VPair kk vv) r =>
         match eq_val (m_heap m) eq_fuel kk k with
         | EqT => r | _ => VPair (VPair kk vv) (rm r) end
       | x => x end in
     match bucket_find (m_heap m) k c with
     | None => raise_v m "~S is not a dictionary" dv
     | Some None => ret k
     | Some (Some _) => ret_to (put_vec (put_vec m b (replace i (rm c) bs)) l [tag; VFix (n - 1); VVec b]) d k end end
 | PDictEntries, [dv] => match dict_parts m dv with
   | None => raise_v m "~S is not a dictionary" dv
   | Some (_, _, _, _, bs) =>
     let fix walk (c : val) (acc : val) : val := match c with
       | VPair (VPair kk vv) r => walk r (VPair (VPair kk vv) acc) | _ => acc end in
     ret (fold_left (fun acc c => walk c acc) bs VNil) end
 | PTaggedp, [a; b] => match a with
   | VVec l => match vec_cells m l with
     | x :: _ => match same x b with Some r => isb r | None => MStuck RIdentity end
     | [] => isb false end
   | _ => isb false end
 | PSealedp, [a] => match a with
   | VSym s => isb (match tget s (m_sealed m) with
     | Some _ => true
     | None => (m_seal_user m && match tget s (m_gfun m) with Some (VClo _) => false | _ => true end)%bool end)
   | _ => isb false end
 | PSealing, [a] => match a with
   | VBool b => ret_to (set_globals m (m_gval m) (m_gfun m) (m_sealed m) b) d a
   | _ => raise_v m "~S is not a boolean" a end
 | PInlineBody, [a] => match a with
   | VSym s => match tget s (m_gfun m) with
     | Some (VClo l) => match tget l (m_heap m) with
       | Some (OClo c _) => ret (code_inline c) | _ => ret VNil end
     | _ => ret VNil end
   | _ => ret VNil end
 | PVectorp, [a] => match a with
   | VVec l => match vec_cells m l with
     | VFix z :: _ => isb (Z.leb 0 z)
     | VReal r :: _ => isb (ge r 0)
     | _ => isb false end
   | _ => isb false end
 | PAbsvector3, [a; b; c] => let '(l, m') := alloc m (OVec [a; b; c]) in ret_to m' d (VVec l)
 | PQuietp, [] => isb (match m_handlers m with h :: _ => h_quiet h | [] => false end)
 | PIntegerp, [a] => isb (match a with
   | VFix _ => true
   | VReal r => match to_Z_exact r with Some _ => true | None => false end
   | _ => false end)
 | PAppend, [a; b] => match vlist a with
   | Some l => ret (fold_right VPair b l)
   | None => raise_s m "attempt to append a non-list" end
 | PArityp, [a; b] => match a, b with
   | VSym s, VFix n => match tget s (m_gfun m) with
     | Some (VClo l) => match tget l (m_heap m) with
       | Some (OClo c _) => isb (Z.eqb (Z.of_N (code_arity c)) n) | _ => isb false end
     | _ => isb false end
   | _, _ => isb false end
 | PInlinedp, [a; b] => match a with
   | VSym s => match tget s (m_gfun m) with
     | Some (VClo l) => match tget l (m_heap m) with
       | Some (OClo c _) =>
         (* C compares the list's address. Structural equality here: a redefinition with
            an identical inline body gives the same behavior through either branch. *)
         match eq_val (m_heap m) eq_fuel (code_inline c) b with
         | EqT => isb true | EqF => isb false | EqIdentity => MStuck RIdentity | EqCycle => MStuck RCyclic end
       | _ => isb false end
     | _ => isb false end
   | _ => isb false end
 | PBytesNew, [a] => match a with
   | VFix n => if orb (Z.ltb n 0) (Z.leb 281474976710656 n) then raise_v m "shen-jit.bytes: ~S is not a valid length" a else
     let '(l, m') := alloc m (OBytes (repeat 0 (Z.to_nat n))) in ret_to m' d (VBytes l)
   | _ => raise_v m "shen-jit.bytes: ~S is not a valid length" a end
 | PBytesp, [a] => isb (match a with VBytes _ => true | _ => false end)
 | PBytesLength, [a] => match a with
   | VBytes l => ret (VFix (Z.of_nat (List.length (bytes_of m l))))
   | _ => raise_v m "bytes: ~S is not a byte buffer" a end
 | (PU8 | PU16 | PU32), [b; i] =>
   let w := match p with PU8 => 1%nat | PU16 => 2%nat | _ => 4%nat end in
   match b with
   | VBytes l => match i with
     | VFix z =>
       if orb (Z.ltb z 0) (Z.ltb (Z.of_nat (List.length (bytes_of m l))) (z + Z.of_nat w))
       then raise_v m "bytes: ~S is not a valid index" i
       else ret (VFix (Z.of_N (le_read (firstn w (skipn (Z.to_nat z) (bytes_of m l))))))
     | _ => raise_v m "bytes: ~S is not a valid index" i end
   | _ => raise_v m "bytes: ~S is not a byte buffer" b end
 | (PSetU8 | PSetU16 | PSetU32), [b; i; x] =>
   let w := match p with PSetU8 => 1%nat | PSetU16 => 2%nat | _ => 4%nat end in
   match b with
   | VBytes l => match i with
     | VFix z =>
       if orb (Z.ltb z 0) (Z.ltb (Z.of_nat (List.length (bytes_of m l))) (z + Z.of_nat w))
       then raise_v m "bytes: ~S is not a valid index" i
       else match x with
         | VFix y =>
           if orb (Z.ltb y 0) (Z.leb (Z.shiftl 1 (8 * Z.of_nat w)) y) then raise_v m "bytes: ~S does not fit" x
           else ret_to (put_bytes m l (splice (Z.to_nat z) (le_bytes w (Z.to_N y)) (bytes_of m l))) d b
         | _ => raise_v m "bytes: ~S does not fit" x end
     | _ => raise_v m "bytes: ~S is not a valid index" i end
   | _ => raise_v m "bytes: ~S is not a byte buffer" b end
 | PStringBytes, [a] => match a with
   | VStr s => let '(l, m') := alloc m (OBytes s) in ret_to m' d (VBytes l)
   | _ => raise_v m "shen-jit.string->bytes: ~S is not a string" a end
 | PBytesString, [a; b; c] => match a with
   | VBytes l => match b, c with
     | VFix s, VFix n =>
       if orb (orb (Z.ltb s 0) (Z.ltb n 0)) (Z.ltb (Z.of_nat (List.length (bytes_of m l))) (s + n))
       then raise_v m "shen-jit.bytes->string: ~S is not a valid range" b
       else ret (VStr (firstn (Z.to_nat n) (skipn (Z.to_nat s) (bytes_of m l))))
     | _, _ => raise_v m "shen-jit.bytes->string: ~S is not a valid range" b end
   | _ => raise_v m "bytes: ~S is not a byte buffer" a end
 | PCopyBytes, [a; b; c; e; n] => match a, c with
   | VBytes la, VBytes lc => match b, e, n with
     | VFix bi, VFix ei, VFix k =>
       if orb (orb (orb (Z.ltb bi 0) (Z.ltb ei 0)) (Z.ltb k 0))
              (orb (Z.ltb (Z.of_nat (List.length (bytes_of m la))) (bi + k)) (Z.ltb (Z.of_nat (List.length (bytes_of m lc))) (ei + k)))
       then raise_v m "shen-jit.copy-bytes: ~S is not a valid count" n
       else let src := firstn (Z.to_nat k) (skipn (Z.to_nat ei) (bytes_of m lc)) in
         ret_to (put_bytes m la (splice (Z.to_nat bi) src (bytes_of m la))) d a
     | _, _, _ => raise_v m "shen-jit.copy-bytes: ~S is not a valid count" n end
   | VBytes _, _ => raise_v m "bytes: ~S is not a byte buffer" c
   | _, _ => raise_v m "bytes: ~S is not a byte buffer" a end
 | PBitNot, [a] => match a with VFix x => ret (VFix (Z.lnot x)) | _ => raise_v m "bit operation: ~S is not an integer" a end
 | PPopcount, [a] => match a with VFix x => ret (VFix (popc 64 (word_of x))) | _ => raise_v m "bit operation: ~S is not an integer" a end
 | PClz, [a] => match a with
   | VFix x => ret (VFix (if Z.eqb x 0 then 62 else clz64 (word_of x)))
   | _ => raise_v m "bit operation: ~S is not an integer" a end
 | PCtz, [a] => match a with
   | VFix x => ret (VFix (if Z.eqb x 0 then 62 else ctz_go 64 (word_of x) 0 - 2))
   | _ => raise_v m "bit operation: ~S is not an integer" a end
 | PBswap32, [a] => match a with
   | VFix x => if orb (Z.ltb x 0) (Z.leb 4294967296 x) then raise_v m "shen-jit.bswap32: ~S does not fit in 32 bits" a
     else ret (VFix (Z.of_N (le_read (rev (le_bytes 4 (Z.to_N x))))))
   | _ => raise_v m "bit operation: ~S is not an integer" a end
 | (PBitAnd | PBitOr | PBitXor | PShiftLeft | PShiftRight | PRotate32), [a; b] => match a, b with
   | VFix x, VFix y => match p with
     | PBitAnd => ret (VFix (Z.land x y)) | PBitOr => ret (VFix (Z.lor x y)) | PBitXor => ret (VFix (Z.lxor x y))
     | _ =>
       if orb (Z.ltb y 0) (Z.ltb 63 y) then raise_v m "bit operation: ~S is not a valid shift" b else
       match p with
       | PShiftLeft => ret (VFix (of_word (u64 (Z.shiftl (word_of x) y))))
       | PShiftRight =>
         let s := if Z.testbit (word_of x) 63 then (word_of x - 18446744073709551616)%Z else word_of x in
         ret (VFix (of_word (Z.land (u64 (Z.shiftr s y)) 18446744073709551612)))
       | _ =>
         if orb (Z.ltb x 0) (Z.leb 4294967296 x) then raise_v m "shen-jit.rotate32: ~S does not fit in 32 bits" a else
         let k := Z.land y 31 in
         ret (VFix (Z.land (Z.lor (Z.shiftl x k) (Z.shiftr x (Z.land (32 - k) 31))) 4294967295)) end end
   | VFix _, _ => raise_v m "bit operation: ~S is not an integer" b
   | _, _ => raise_v m "bit operation: ~S is not an integer" a end
 | PDecimal, [s; e] => match s, e with
   | VStr x, VFix ex =>
     let '(mant, own) := (fix split (l acc : text) : text * Z := match l with
       | 101 :: r =>
         let '(neg, ds) := match r with 45 :: q => (true, q) | 43 :: q => (false, q) | _ => (false, r) end in
         let '(v, _, _) := scan_digits ds 0 0 in (rev acc, if neg then (- v)%Z else v)
       | c :: r => split r (c :: acc)
       | [] => (rev acc, 0%Z) end) x [] in
     ret (VReal (parse_decimal mant (ex + own)))
   | _, _ => raise_v m "shen-jit.decimal: ~S is not a string and an exponent" s end
 | PPvar, [a] => match a with
   | VFix z => if orb (Z.ltb z 0) (Z.ltb 72057594037927935 z) then raise_v m "shen-jit.pvar: ~S is not a valid offset" a
     else ret (VPvar z)
   | _ => raise_v m "shen-jit.pvar: ~S is not a valid offset" a end
 | PPvarp, [a] => isb (match a with VPvar _ => true | _ => false end)
 | PPvarOffset, [a] => match a with
   | VPvar z => ret (VFix z) | _ => raise_v m "shen-jit.pvar-offset: ~S is not a Prolog variable" a end
 | PDeref, [a; b; mark] =>
   let fix go (fuel : nat) (x : val) : move := match fuel with
     | O => MStuck RCyclic
     | S f => match x with
       | VPvar off => match b with
         | VVec l => match nth_error (vec_cells m l) (Z.to_nat off) with
           | Some bound => match same bound mark with
             | Some true => ret x
             | Some false => go f bound
             | None => MStuck RIdentity end
           | None => raise_v m "shen-jit.deref: ~S has no binding here" x end
         | _ => raise_v m "shen-jit.deref: ~S has no binding here" x end
       | _ => ret x end end in
   go (S (match b with VVec l => List.length (vec_cells m l) | _ => O end)) a
 | PSamep, [a; b] => match same a b with Some r => isb r | None => MStuck RIdentity end
 | PPointerp, [_] => isb false
 | PRaiseCond, [] => raise_s m "cond: no clause applies"
 | PGetTime, [a] => match a with
   | VSym s =>
     if Pos.eqb s S_run then MIO (JTime true) (fun r => match r with
       | JTimeIs b => set_stack m (swrite m d (VReal b)) | _ => m end)
     else if Pos.eqb s S_unix then MIO (JTime false) (fun r => match r with
       | JTimeIs b => set_stack m (swrite m d (VReal b)) | _ => m end)
     else raise_v m "get-time: ~S is not run or unix" a
   | _ => raise_v m "get-time: ~S is not run or unix" a end
 | POpen, [path; dir] =>
   match path with
   | VStr ps =>
     let home := match tget S__home_directory_ (m_gval m) with Some (VStr h) => h | _ => [] end in
     let go ds := MIO (JOpen (home ++ ps) ds) (fun r => match r with
       | JOpened h => let '(l, m') := alloc m (OStream h ds true) in set_stack m' (swrite m' d (VStream l))
       | _ => match raise_v m "open: cannot open ~S" path with MTau m' => m' | _ => m end end) in
     match dir with
     | VSym s =>
       if Pos.eqb s S_out then go SOut
       else if Pos.eqb s S_in then go SIn
       else raise_v m "open: the direction ~S is not in or out" dir
     | _ => raise_v m "open: the direction ~S is not in or out" dir end
   | _ => raise_v m "open: ~S is not a string" path end
 | PClose, [s] => match s with
   | VStream l => match tget l (m_heap m) with
     | Some (OStream h dr true) =>
       (* The stream is closed either way; a failed flush or fclose raises (prims.c, 0.4). *)
       let m1 := set_heap m (tset l (OStream h dr false) (m_heap m)) in
       MIO (JClose h) (fun r => match r with
         | JFailed => match raise_s m1 "close: the write failed" with MTau m' => m' | _ => m1 end
         | _ => set_stack m1 (swrite m1 d VNil) end)
     | _ => ret VNil end
   | _ => raise_v m "close: ~S is not a stream" s end
 | PReadByte, [s] => match s with
   | VStream l => match tget l (m_heap m) with
     | Some (OStream h SIn true) => MIO (JRead h) (fun r => match r with
       | JByte b => set_stack m (swrite m d (VFix (Z.of_N b)))
       (* 0.6: a read error raises (prims.c read_byte); the binary appends strerror. *)
       | JReadFailed => match raise_s m "read-byte: the read failed" with MTau m' => m' | _ => m end
       | _ => set_stack m (swrite m d (VFix (-1))) end)
     | _ => raise_v m "read-byte: ~S is not an open input stream" s end
   | _ => raise_v m "read-byte: ~S is not an open input stream" s end
 | PWriteByte, [b; s] => match s with
   | VStream l => match tget l (m_heap m) with
     | Some (OStream h SOut true) => match b with
       | VFix z =>
         if (Z.leb 0 z && Z.leb z 255)%bool
         (* fputc returning EOF raises (prims.c, 0.4); buffering decides when the environment says so. *)
         then MIO (JWrite h (Z.to_N z)) (fun r => match r with
           | JFailed => match raise_s m "write-byte: the write failed" with MTau m' => m' | _ => m end
           | _ => set_stack m (swrite m d b) end)
         else raise_v m "write-byte: ~S is not a byte" b
       | _ => raise_v m "write-byte: ~S is not a byte" b end
     | _ => raise_v m "write-byte: ~S is not an open output stream" s end
   | _ => raise_v m "write-byte: ~S is not an open output stream" s end
 | PReadFile, [path; as_list] => match path with
   | VStr ps =>
     let home := match tget S__home_directory_ (m_gval m) with Some (VStr h) => h | _ => [] end in
     MIO (JReadFile (home ++ ps)) (fun r => match r with
       | JFile bs =>
         set_stack m (swrite m d (match as_list with
           | VBool true => of_list (map (fun b => VFix (Z.of_N b)) bs)
           | _ => VStr bs end))
       (* 0.6: a read error after the open raises, with no partial data (prims.c read_file). *)
       | JReadFailed => match raise_s m "read-file: the read failed" with MTau m' => m' | _ => m end
       | _ => match raise_v m "open: cannot open ~S" path with MTau m' => m' | _ => m end end)
   | _ => raise_v m "open: ~S is not a string" path end
 | PWriteBytes, [b; i; n; s] =>
   (* 0.6, prims.c write_bytes: the buffer, then the range, then the stream, then one fwrite,
      which N = 0 skips. It returns N. *)
   match b with
   | VBytes l => match i, n with
     | VFix iz, VFix nz =>
       if orb (orb (Z.ltb iz 0) (Z.ltb nz 0)) (Z.ltb (Z.of_nat (List.length (bytes_of m l))) (iz + nz))
       then raise_v m "shen-jit.write-bytes: ~S is not a valid range" i
       else match s with
         | VStream ls => match tget ls (m_heap m) with
           | Some (OStream h SOut true) =>
             if Z.eqb nz 0 then ret n
             else MIO (JWrites h (firstn (Z.to_nat nz) (skipn (Z.to_nat iz) (bytes_of m l)))) (fun r => match r with
               | JFailed => match raise_s m "shen-jit.write-bytes: the write failed" with MTau m' => m' | _ => m end
               | _ => set_stack m (swrite m d n) end)
           | _ => raise_v m "shen-jit.write-bytes: ~S is not an open output stream" s end
         | _ => raise_v m "shen-jit.write-bytes: ~S is not an open output stream" s end
     | _, _ => raise_v m "shen-jit.write-bytes: ~S is not a valid range" i end
   | _ => raise_v m "bytes: ~S is not a byte buffer" b end
 | q, _ => if is_excluded q then MStuck (RExcluded q) else MStuck RArgs end.

(* ---------- entering a procedure ---------- *)
Definition enter (E : env) (m : machine) (callee : val) (count : N) (st : tree val) (fp : N) (ks : list cont) : move :=
 match callee with
 | VClo l => match tget l (m_heap m) with
   | Some (OClo c _) =>
     let m' := set_ctl m st fp c (code_ins c) ks in
     let msg (_ : unit) := match code_name c with
       | VSym s => text_of_sym s ++ t ": expected " ++ z_digits (Z.of_N (code_arity c))
                    ++ t (if N.eqb (code_arity c) 1 then " argument, got " else " arguments, got ")
                    ++ z_digits (Z.of_N count)
       | _ => t "wrong number of arguments" end in
     let checked r :=
       if e_stack E (fp + code_frame c) then raise_s m' "stack overflow" else MTau (set_rest m' r) in
     if N.eqb count (code_arity c) then checked (code_ins c)
     else match code_entry c with
       | Some (n, lb) =>
         if N.eqb count n then
           match find_label lb (code_ins c) with Some r => checked r | None => MStuck RBadLabel end
         else raise m' (msg tt) VCleared
       | None => raise m' (msg tt) VCleared end
   | _ => MStuck RBadCode end
 | _ => MStuck RBadCode end.

Definition callee_named (m : machine) (f : positive) : sum val move :=
 match tget f (m_gfun m) with
 | Some (VClo l) => inl (VClo l)
 | _ => inr (raise_v m "undefined function ~S" (VSym f)) end.
Definition callee_value (m : machine) (a : N) : sum val move :=
 match sread m (a + 1) with
 | Some (VClo l) => inl (VClo l)
 | Some VCleared | None => inr (raise_v m "undefined function ~S" VCleared)
 | Some v => inr (raise_v m "~S is not a function" v) end.

Definition do_call (E : env) (m : machine) (d a n : N) (r : list instr) (cv : sum val move) : move :=
 match cv with
 | inr mv => mv
 | inl callee =>
   let st := tset (skey (m_fp m + a + 1)) callee (m_stack m) in
   enter E m callee n st (m_fp m + a) (Cont (m_code m) r d a :: m_conts m) end.

Fixpoint move_args (st : tree val) (fp a : N) (n : nat) (i : N) : option (tree val) := match n with
 | O => Some st
 | S n =>
   match tget (skey (fp + a + 2 + i)) st with
   | Some v => move_args (tset (skey (fp + 2 + i)) v st) fp a n (i + 1)
   | None => None end end.
Definition do_tail (E : env) (m : machine) (a n : N) (cv : sum val move) : move :=
 match cv with
 | inr mv => mv
 | inl callee =>
   match (if N.eqb a 0 then Some (m_stack m) else move_args (m_stack m) (m_fp m) a (N.to_nat n) 0) with
   | Some st => enter E m callee n (tset (skey (m_fp m + 1)) callee st) (m_fp m) (m_conts m)
   | None => MStuck (RBadSlot a) end end.

Definition read_op (m : machine) (o : operand) : option val := match o with
 | OSlot s => sread m s
 | OConst k => nth_error (code_consts (m_code m)) (N.to_nat k) end.

Definition do_return (m : machine) (v : val) : move :=
 match m_conts m with
 | [] => MFinal (FReturn v) m
 | k :: ks =>
   let fp := m_fp m - k_window k in
   MTau (set_ctl m (tset (skey (fp + k_dst k)) v (m_stack m)) fp (k_code k) (k_rest k) ks) end.

(* ---------- one step ---------- *)
Definition next (E : env) (ptab : tree (prim * nat)) (m : machine) : move :=
 match m_rest m with
 | [] => MStuck RFallOff
 | i :: r =>
   let m := set_rest m r in
   match i with
   | IMove d s => match sread m s with
     | Some v => MTau (set_stack m (swrite m d v)) | None => MStuck (RBadSlot s) end
   | IConst d k => match nth_error (code_consts (m_code m)) (N.to_nat k) with
     | Some v => MTau (set_stack m (swrite m d v)) | None => MStuck RBadConst end
   | ICapture d c => match sread m 1 with
     | Some (VClo l) => match tget l (m_heap m) with
       | Some (OClo _ caps) => match nth_error caps (N.to_nat c) with
         | Some v => MTau (set_stack m (swrite m d v)) | None => MStuck RBadCapture end
       | _ => MStuck RBadCapture end
     | _ => MStuck RBadCapture end
   | IClosure d c ss =>
     match nth_error (code_codes (m_code m)) (N.to_nat c), all_some (map (sread m) ss) with
     | Some nc, Some caps =>
       if e_oom E (m_allocs m) then raise_s m "out of memory" else
       let '(l, m') := alloc m (OClo nc caps) in MTau (set_stack m' (swrite m' d (VClo l)))
     | None, _ => MStuck RBadCode
     | _, None => MStuck (RBadSlot d) end
   | IPrim d p ops =>
     match all_some (map (read_op m) ops) with
     | None => MStuck (RBadSlot d)
     | Some args =>
       if (allocates p && e_oom E (m_allocs m))%bool then raise_s m "out of memory"
       else prim_step E ptab m d p args end
   | ILabel _ | IInline _ _ | IEntry _ _ => MTau m
   | IJump l => match find_label l (code_ins (m_code m)) with
     | Some r' => MTau (set_rest m r') | None => MStuck RBadLabel end
   | IJumpIfFalse o l => match read_op m o with
     | Some (VBool true) => MTau m
     | Some (VBool false) => match find_label l (code_ins (m_code m)) with
       | Some r' => MTau (set_rest m r') | None => MStuck RBadLabel end
     | Some v => raise_v m "~S is not a boolean" v
     | None => MStuck (RBadSlot 0) end
   | ICall d a f n | ICallSealed d a f n => do_call E m d a n r (callee_named m f)
   | ICallValue d a n => do_call E m d a n r (callee_value m a)
   | ITail a f n | ITailSealed a f n => do_tail E m a n (callee_named m f)
   | ITailValue a n => do_tail E m a n (callee_value m a)
   | IReturn o => match read_op m o with
     | Some v => do_return m v | None => MStuck (RBadSlot 0) end
   | IPushHandler l =>
     match find_label l (code_ins (m_code m)) with
     | None => MStuck RBadLabel
     | Some after =>
       let quiet := match after with IException _ :: _ => false | _ => true end in
       MTau (set_handlers m (Handler (m_code m) l (m_fp m) (m_conts m) quiet :: m_handlers m)) end
   | IPopHandler => match m_handlers m with
     | _ :: hs => MTau (set_handlers m hs) | [] => MStuck RBadCode end
   | IException d => MTau (set_stack m (swrite m d (m_exn m)))
   | IJumpUnlessEntry s n l =>
     let jump (_ : unit) := match find_label l (code_ins (m_code m)) with
       | Some r' => MTau (set_rest m r') | None => MStuck RBadLabel end in
     match sread m s with
     | Some (VClo c) => match tget c (m_heap m) with
       | Some (OClo cd _) => match code_entry cd with
         | Some (x, _) => if N.eqb x n then MTau m else jump tt
         | None => jump tt end
       | _ => jump tt end
     | Some _ => jump tt
     | None => MStuck (RBadSlot s) end
   end end.

(* ---------- running ---------- *)
Definition boot_code : code := Code VNil 0 None 2 [] [IReturn (OConst 0)] [] VNil.
Definition empty_machine : machine :=
 {| m_stack := Leaf; m_fp := 0; m_code := boot_code; m_rest := []; m_conts := [];
    m_handlers := []; m_exn := VNil; m_heap := Leaf; m_next := xH;
    m_gval := Leaf; m_gfun := Leaf; m_sealed := Leaf; m_seal_user := false; m_allocs := 0 |}.

Inductive result := RDone (o : final) (m : machine) | RStuck (why : stuck) | RNeedsIO | ROutOfFuel.

Fixpoint run (E : env) (ptab : tree (prim * nat)) (fuel : nat) (m : machine) : result := match fuel with
 | O => ROutOfFuel
 | S f => match next E ptab m with
   | MTau m' => run E ptab f m'
   | MIO _ _ => RNeedsIO
   | MFinal o m' => RDone o m'
   | MStuck w => RStuck w end end.

(* Call a closure with no arguments on a fresh top level, keeping the store. *)
Definition start (E : env) (m : machine) (callee : val) : move :=
 let st := tset (skey 1) callee Leaf in
 enter E (set_handlers m []) callee 0 st 0 [].
End JitBytecode.
