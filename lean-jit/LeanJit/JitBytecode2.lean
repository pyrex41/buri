import LeanJit.JitBytecode1
/-! Port of `rocq/JitBytecode.v`, part 2 (raising, loader, install). -/
namespace JitBytecode
open JitFloat val prim operand instr code obj stream_dir move final stuck

-- ---------- raising ----------
def find_label (l : Nat) : List instr → Option (List instr)
  | [] => none
  | ILabel x :: r => if x == l then some r else find_label l r
  | _ :: r => find_label l r

def raise (m : machine) (msg : text) (v : val) : move :=
  match m.m_handlers with
  | [] => let (l, m') := alloc m (OExn msg v); MFinal (FError (VExn l)) m'
  | h :: hs =>
    match find_label h.h_label (code_ins h.h_code) with
    | none => MStuck RBadLabel
    | some r =>
      if h.h_quiet then
        MTau (set_exn (set_ctl (set_handlers m hs) m.m_stack h.h_fp h.h_code r h.h_conts) VNil)
      else
        let (l, m') := alloc m (OExn msg v)
        MTau (set_exn (set_ctl (set_handlers m' hs) m'.m_stack h.h_fp h.h_code r h.h_conts) (VExn l))
def raise_s (m : machine) (s : String) : move := raise m (t s) VCleared
def raise_v (m : machine) (s : String) (v : val) : move := raise m (t s) v

def ret_to (m : machine) (d : Nat) (v : val) : move := MTau (set_stack m (swrite m d v))
def boolean (m : machine) (d : Nat) (b : Bool) := ret_to m d (VBool b)

-- ---------- installing code (loader.c) ----------
inductive loaded (A : Type) | LOk (a : A) | LErr (msg : String)
export loaded (LOk LErr)
def small_int (v : val) (limit : Int) : Option Nat := match v with
  | VFix z => if decide (0 ≤ z) && decide (z < limit) then some z.toNat else none
  | _ => none
def lim (n : Nat) : Int := n
def operand_of (v : val) (frame nconst : Nat) : Option operand := match v with
  | VPair (VSym c) (VPair k VNil) =>
    if c.eqb S_const then (small_int k (lim nconst)).map OConst else none
  | VPair _ _ => none
  | _ => (small_int v (lim frame)).map OSlot
def all_some {A} : List (Option A) → Option (List A)
  | [] => some []
  | none :: _ => none
  | some x :: r => (all_some r).map (x :: ·)
def prim_lookup (s : Pos) : List (String × prim × Nat) → Option (prim × Nat)
  | [] => none
  | (n, p, a) :: r => if (sym n).eqb s then some (p, a) else prim_lookup s r

def b2 : Int := 4294967295
def sn (v : val) (f : Nat) := small_int v (lim f)
def window_ok (a count frame : Nat) : Bool := decide (a + 1 + count < frame)

def encode (ptab : tree (prim × Nat)) (insn : val) (frame nconst ncode : Nat) : loaded instr :=
  match vlist insn with
  | none | some [] => LErr "malformed instruction"
  | some (VSym op :: args) =>
    let bad := LErr "bad operand"
    let cnt := LErr "wrong operand count"
    let win := LErr "call window outside the frame"
    let iss (s : String) := op.eqb (sym s)
    if iss "move" then match args with
      | [d, s] => match sn d frame, sn s frame with | some d, some s => LOk (IMove d s) | _, _ => bad
      | _ => cnt
    else if iss "const" then match args with
      | [d, k] => match sn d frame, sn k nconst with | some d, some k => LOk (IConst d k) | _, _ => bad
      | _ => cnt
    else if iss "capture" then match args with
      | [d, i] => match sn d frame, small_int i 256 with | some d, some i => LOk (ICapture d i) | _, _ => bad
      | _ => cnt
    else if iss "closure" then match args with
      | d :: c :: ss => match sn d frame, sn c ncode, all_some (ss.map (fun s => sn s frame)) with
        | some d, some c, some ss => LOk (IClosure d c ss) | _, _, _ => bad
      | _ => cnt
    else if iss "prim" then match args with
      | d :: VSym p :: os =>
        match sn d frame with
        | none => bad
        | some d =>
          match tget p ptab with
          | some (pr, a) =>
            if a == os.length then
              match all_some (os.map (fun o => operand_of o frame nconst)) with
              | some os => LOk (IPrim d pr os) | none => bad
            else LErr "unknown primitive or wrong arity"
          | none => LErr "unknown primitive or wrong arity"
      | _ :: _ :: _ => LErr "unknown primitive or wrong arity"
      | _ => cnt
    else if iss "label" then match args with
      | [l] => match small_int l b2 with | some l => LOk (ILabel l) | none => bad
      | _ => cnt
    else if iss "jump" then match args with
      | [l] => match small_int l b2 with | some l => LOk (IJump l) | none => bad
      | _ => cnt
    else if iss "jump-if-false" then match args with
      | [o, l] => match operand_of o frame nconst, small_int l b2 with
        | some o, some l => LOk (IJumpIfFalse o l) | _, _ => bad
      | _ => cnt
    else if iss "call" || iss "call-sealed" then match args with
      | [d, a, VSym f, n] => match sn d frame, sn a frame, small_int n 256 with
        | some d, some a, some n =>
          if window_ok a n frame then LOk (if iss "call" then ICall d a f n else ICallSealed d a f n) else win
        | _, _, _ => bad
      | [_, _, _, _] => bad
      | _ => cnt
    else if iss "call-value" then match args with
      | [d, a, n] => match sn d frame, sn a frame, small_int n 256 with
        | some d, some a, some n => if window_ok a n frame then LOk (ICallValue d a n) else win
        | _, _, _ => bad
      | _ => cnt
    else if iss "tail-call" || iss "tail-call-sealed" then match args with
      | [a, VSym f, n] => match sn a frame, small_int n 256 with
        | some a, some n =>
          if window_ok a n frame then LOk (if iss "tail-call" then ITail a f n else ITailSealed a f n) else win
        | _, _ => bad
      | [_, _, _] => bad
      | _ => cnt
    else if iss "tail-call-value" then match args with
      | [a, n] => match sn a frame, small_int n 256 with
        | some a, some n => if window_ok a n frame then LOk (ITailValue a n) else win
        | _, _ => bad
      | _ => cnt
    else if iss "return" then match args with
      | [o] => match operand_of o frame nconst with | some o => LOk (IReturn o) | none => bad
      | _ => cnt
    else if iss "push-handler" then match args with
      | [l] => match small_int l b2 with | some l => LOk (IPushHandler l) | none => bad
      | _ => cnt
    else if iss "pop-handler" then match args with | [] => LOk IPopHandler | _ => cnt
    else if iss "exception" then match args with
      | [d] => match sn d frame with | some d => LOk (IException d) | none => bad
      | _ => cnt
    else if iss "entry" then match args with
      | [n, l] => match small_int n 256, small_int l b2 with
        | some n, some l => LOk (IEntry n l) | _, _ => bad
      | _ => cnt
    else if iss "jump-unless-entry" then match args with
      | [s, n, l] => match sn s frame, small_int n 256, small_int l b2 with
        | some s, some n, some l => LOk (IJumpUnlessEntry s n l) | _, _, _ => bad
      | _ => cnt
    else if iss "inline" then match args with
      | [VSym f, n] => match small_int n b2 with | some n => LOk (IInline f n) | none => bad
      | [_, _] => bad
      | _ => cnt
    else LErr "unknown instruction"
  | some _ => LErr "unknown instruction"

def excluded_ops : List String :=
 ["loop","again","real-number","real-box","real-move","real-neg","real-abs","real-sqrt","real+","real-","real*","real/"
 ,"real-unless<","real-unless>","real-unless<=","real-unless>=","real-unless=","real-load","real-store"
 ,"real-load-at","real-store-at","real-from-word","word-from-real","word-number","word-box","word-move"
 ,"word+","word-","word*","word-and","word-or","word-xor","word-shl","word-shr","word-sar","word-rotl","word-rotr"
 ,"word-unless<","word-unless>","word-unless<=","word-unless>=","word-unless=","word-unless-u<","word-unless-u>"
 ,"word-unless-u<=","word-unless-u>=","word-load8","word-load16","word-load32","word-load-s32","word-load64"
 ,"word-store8","word-store16","word-store32","word-store64"]

def target_of : instr → Option Nat
  | IJump l | IPushHandler l | IJumpIfFalse _ l | IEntry _ l | IJumpUnlessEntry _ _ l => some l
  | _ => none
def labels_of : List instr → List Nat
  | [] => [] | ILabel l :: r => l :: labels_of r | _ :: r => labels_of r
def nodup_N : List Nat → Bool
  | [] => true | x :: r => !(r.any (x == ·)) && nodup_N r
def is_entry : instr → Bool | IEntry _ _ => true | _ => false
def is_transfer : instr → Bool
  | IReturn _ | IJump _ | ITail _ _ _ | ITailSealed _ _ _ | ITailValue _ _ => true | _ => false
def check_control (iss : List instr) : Bool :=
  match iss with
  | [] => false
  | first :: rest =>
    let ls := labels_of iss
    nodup_N ls
    && iss.all (fun i => match target_of i with | some l => ls.any (l == ·) | none => true)
    && !(rest.any is_entry)
    && is_transfer (iss.getLastD first)

def map_loaded {A B} (f : A → loaded B) : List A → loaded (List B)
  | [] => LOk []
  | x :: r => match f x with
    | LErr e => LErr e
    | LOk y => match map_loaded f r with | LErr e => LErr e | LOk ys => LOk (y :: ys)

def build_code (ptab : tree (prim × Nat)) : Nat → val → loaded code
  | 0, _ => LErr "malformed code object"
  | f + 1, form =>
    match vlist form with
    | some (VSym hd :: name :: arity :: frame :: consts :: insns :: codes :: more) =>
      if !(hd.eqb S_code) then LErr "malformed code object" else
      match more, small_int arity 256, small_int frame 1048576, vlist consts, vlist insns, vlist codes with
      | [], some ar, some fr, some cs, some iss, some ns
      | [_], some ar, some fr, some cs, some iss, some ns =>
        if fr < ar + 2 then LErr "malformed code object" else
        let inl := match more with | [x] => x | _ => VNil
        match map_loaded (build_code ptab f) ns with
        | LErr e => LErr e
        | LOk nested =>
          match map_loaded (fun i => encode ptab i fr cs.length ns.length) iss with
          | LErr e => LErr e
          | LOk ins =>
            if !(check_control ins) then LErr "bad control flow: labels or the final instruction" else
            match ins with
            | IEntry n l :: _ =>
              if decide (n ≤ ar) || decide (fr < n + 2)
              then LErr "entry outside the frame or not above the arity"
              else LOk (Code name ar (some (n, l)) fr cs ins nested inl)
            | _ => LOk (Code name ar none fr cs ins nested inl)
      | _, _, _, _, _, _ => LErr "malformed code object"
    | _ => LErr "malformed code object"

def prim_tree : tree (prim × Nat) :=
  prim_table.foldl (fun tr e => let (n, p, a) := e; tset (sym n) (p, a) tr) Leaf

def install (ptab : tree (prim × Nat)) (m : machine) (d : Nat) (form : val) : move :=
  let build (c : val) : Sum String (Pos × machine) :=
    match build_code ptab 64 c with
    | LErr e => .inl e
    | LOk code => .inr (alloc m (OClo code []))
  match vlist form with
  | some [VSym h, VSym name, c] =>
    if h.eqb S_defun then
      match tget name m.m_sealed with
      | some _ => raise_v m "~S is sealed and cannot be redefined" (VSym name)
      | none =>
        match build c with
        | .inl e => raise_s m e
        | .inr (l, m') =>
          let se := if m'.m_seal_user then tset name () m'.m_sealed else m'.m_sealed
          let m'' := set_globals m' m'.m_gval (tset name (VClo l) m'.m_gfun) se m'.m_seal_user
          ret_to m'' d (VSym name)
    else raise_s m "install: expected (defun Name Code) or a code object"
  | _ =>
    match form with
    | VPair (VSym h) _ =>
      if h.eqb S_code then
        match build form with
        | .inl e => raise_s m e
        | .inr (l, m') => ret_to m' d (VClo l)
      else raise_s m "install: expected (defun Name Code) or a code object"
    | _ => raise_s m "install: expected (defun Name Code) or a code object"

end JitBytecode
