(* Shen/JIT Phase 1: the Shen/JIT semantic profile, in the slots of KLValue.profile, its
   options in KLPort.port_rules, and the table of where each deviation is stated. Stating them
   does not show the port refines the semantics under them: that is Phase 2 onward. *)
From Coq Require Import List ZArith NArith String Bool.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode.
Import ListNotations.
Module JitProfile.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort.
Local Open Scope string_scope.

(* Numbers cross the two semantics by these conversions. *)
Definition double_of (n : num) : N := match n with
 | NInt z => JitFloat.JitFloat.of_Z z | NFloat b => b end.

(* + - * / with a real operand. A zero divisor, integer or real, is an error (prims.c
   arithmetic), so PDiv with a zero real divisor is outside the domain. *)
Definition jit_inexact_op (p : prim) (a b : num) : option num :=
 let x := double_of a in let y := double_of b in
 match p with
 | PAdd => Some (NFloat (JitFloat.JitFloat.add x y))
 | PSub => Some (NFloat (JitFloat.JitFloat.sub x y))
 | PMul => Some (NFloat (JitFloat.JitFloat.mul x y))
 | PDiv => if JitFloat.JitFloat.is_zero y then None else Some (NFloat (JitFloat.JitFloat.div x y))
 | _ => None end.

(* Comparison with a real operand is exact: no rounding of the integer (prims.c, compare_fix_real).
   NaN compares false. *)
Definition jit_order (p : prim) (c : option comparison) : bool := match p, c with
 | PGt, Some Gt | PLt, Some Lt | PEqual, Some Eq => true
 | PGe, Some (Gt | Eq) | PLe, Some (Lt | Eq) => true
 | _, _ => false end.
Definition flip (c : option comparison) : option comparison := match c with
 | Some Lt => Some Gt | Some Gt => Some Lt | c => c end.
Definition jit_inexact_cmp (p : prim) (a b : num) : bool :=
 match a, b with
 | NInt x, NFloat y => jit_order p (JitBytecode.JitBytecode.compare_fix_real x y)
 | NFloat x, NInt y => jit_order p (flip (JitBytecode.JitBytecode.compare_fix_real y x))
 | _, _ => jit_order p (JitFloat.JitFloat.compare (double_of a) (double_of b)) end.

Definition jit_int_div (x y : Z) : num :=
 NFloat (JitFloat.JitFloat.div (JitFloat.JitFloat.of_Z x) (JitFloat.JitFloat.of_Z y)).

Definition jit_str_other (v : value) : option Observation.Observation.text := match v with
 | VStr s => Some ([34%N] ++ s ++ [34%N])%list
 | VNil => Some (of_string "()")
 | VCons _ _ => Some (of_string "#<pair>")
 | VVec _ => Some (of_string "#<absvector>")
 | VStream _ => Some (of_string "#<stream>")
 | VExn _ => Some (of_string "#<exception>")
 | VLam _ _ _ | VFrozen _ _ | VPartial _ _ => Some (of_string "#<procedure>")
 | _ => None end.

(* Messages are not a compatibility requirement (docs/semantics.md section 8), and most
   name the offending value, which exn does not carry: Ledger OB-JIT-ERROR-TEXT. *)
Definition jit_sys_message (x : exn) : Observation.Observation.text := match x with
 | XDivZero => of_string "division by zero"
 | XCondFail => of_string "cond: no clause applies"
 | _ => of_string "error" end.

(* The clock answers in binary64. RTime carries an integer, so here that integer is the bit pattern. *)
Definition jit_time (_ : Observation.Observation.text) (z : Z) : option num :=
 if (Z.leb 0 z && Z.ltb z 18446744073709551616)%bool then Some (NFloat (Z.to_N z)) else None.

Definition jit_profile : profile := Profile
 jit_inexact_op jit_inexact_cmp jit_int_div
 JitFloat.JitFloat.format_real
 jit_str_other jit_sys_message
 (VSym (of_string "shen.fail!"))
 jit_time
 None None.

Theorem jit_division_by_zero_real : forall a b,
 JitFloat.JitFloat.is_zero (double_of b) = true -> jit_inexact_op PDiv a b = None.
Proof.
 intros a b H. unfold jit_inexact_op. cbv zeta. rewrite H. reflexivity.
Qed.

Theorem jit_absvector_fill : absvector_fill jit_profile = VSym (of_string "shen.fail!").
Proof. reflexivity. Qed.

(* --- The options --- *)
(* n->string from 0.6: a byte as itself, any other scalar value as its UTF-8 bytes (prims.c P_N_STRING),
   the same function as the bytecode's. *)
Definition jit_char_text (z : Z) : option Observation.Observation.text := JitBytecode.JitBytecode.utf8_of z.

(* Names defun refuses: every primitive of the table, the special forms, do, thaw and protect (semantics.md s10,
   lower.shen's fixed?). Which kernel names are sealed comes from the image, so it is a parameter here; relating it
   to the image is OB-JIT-IMAGE. *)
Definition is_fixed_name (f : name) : bool :=
 existsb (fun e => match e with (nm, _, _) => text_eqb f (of_string nm) end) JitBytecode.JitBytecode.prim_table
 || keyword f || text_eqb f (of_string "do") || text_eqb f (of_string "thaw") || text_eqb f (of_string "protect").

(* --- Port primitives: a proposal, not in jit_rules (OB-JIT-PORT-PRIMS) ---
   Census (pass_census-style walk of the 955 erased v0.6 witnesses, not evidence): 35 operators
   of NPrim nodes are not KL primitives (port_prims_census below). jit_rules keeps port_prim at
   `fun _ => None`, so each of them still raises XUndefinedFun and every definition that reaches
   one stays a named residual. What follows is the candidate meaning of 18 of them, following
   src/runtime/prims.c as JitBytecode.prim_step models it, in KL values. Wiring in the 14 that need no hash is the one
   line `(fun _ => None)` -> `jit_port_prims_core` at the end of jit_rules; all 18 also need `hash` as a
   parameter of jit_rules, as `sealed` is. Either waits on Reuben's decision. The other 17, and shen-jit.inlined? and shen-jit.arity?, have no candidate:
   jit_port_prims_residual says why.

   Choices a reviewer has to accept, each a difference from the binary or a parameter:
   - Errors raise XUser with prims.c's message, the offending value not printed (messages are
     not compared: semantics.md s8, OB-JIT-ERROR-TEXT).
   - hash, and so each dictionary's bucket order, is a parameter: the environment's sj_hash.
   - same? and tagged? compare by identity, which KL has for symbols, integers, booleans, (),
     vectors, streams and tagged closures; on pairs, strings, reals, exceptions and partial
     applications it is undefined, an OWrong, as the bytecode's RIdentity is.
   - Dictionary keys compare by = with closure identity on (eq_depth_r reads only
     object_identity), where the bytecode's eq_val would be stuck on identity.
   - Allocation checks the profile's heap limit, as absvector does. *)
Definition pp_rule := profile -> list value -> store -> presult.
Definition pp_raise (msg : string) : presult := throw (XUser (of_string msg)).
Definition pp_bool (b : bool) (s : store) : presult := ret (VBool b) s.
(* Only object_identity of these rules is read, by kl_eq_r. *)
Definition id_eq_rules : port_rules := PortRules
 None (fun _ => None) true false (fun _ _ => true) (fun _ => true) false (fun _ => None) (fun _ => None).
Definition pp_eq (P : profile) (s : store) (a b : value) : option bool := kl_eq_r id_eq_rules P (heap s) a b.

Definition pp_same (a b : value) : option bool := match a, b with
 | VNum (NInt x), VNum (NInt y) => Some (Z.eqb x y)
 | VNum (NFloat _), VNum (NFloat _) => None
 | VSym x, VSym y => Some (text_eqb x y)
 | VBool x, VBool y => Some (Bool.eqb x y)
 | VNil, VNil => Some true
 | VVec x, VVec y => Some (Nat.eqb x y)
 | VStream x, VStream y => Some (N.eqb x y)
 | VCons _ _, VCons _ _ | VStr _, VStr _ | VExn _, VExn _ | VPartial _ _, VPartial _ _ => None
 | (VLam _ _ _ | VFrozen _ _), (VLam _ _ _ | VFrozen _ _) => opaque_eq a b
 | _, _ => Some false end.
Definition pp_identity (r : option bool) (s : store) : presult := match r with
 | Some b => pp_bool b s | None => PDone (OWrong (of_string "identity-undefined")) end.

Fixpoint kl_list (v : value) : option (list value) := match v with
 | VNil => Some [] | VCons a d => option_map (cons a) (kl_list d) | _ => None end.
Definition cells (s : store) (l : nat) : list value := nth l (heap s) [].
Definition alloc_vec (P : profile) (xs : list value) (s : store) : presult :=
 if alloc_ok P (heap s) (List.length xs)
 then ret (VVec (List.length (heap s))) (Store (heap s ++ [xs]) (gvals s) (gfuns s))
 else PDone (OFail Observation.Observation.RHeap).
Definition put_cells (s : store) (l : nat) (xs : list value) : store :=
 Store (replace_nth l xs (heap s)) (gvals s) (gfuns s).

(* --- each operator --- *)
Definition pp_symbolp : pp_rule := fun _ args s => match args with
 | [VSym _] => pp_bool true s | _ => pp_bool false s end.
Definition pp_integerp : pp_rule := fun _ args s => match args with
 | [VNum (NInt _)] => pp_bool true s
 | [VNum (NFloat r)] => pp_bool (match JitFloat.JitFloat.to_Z_exact r with Some _ => true | None => false end) s
 | _ => pp_bool false s end.
Definition pp_append : pp_rule := fun _ args s => match args with
 | [a; b] => match kl_list a with
   | Some l => ret (fold_right VCons b l) s | None => pp_raise "attempt to append a non-list" end
 | _ => pp_raise "attempt to append a non-list" end.
Definition pp_absvector3 : pp_rule := fun P args s => match args with
 | [a; b; c] => alloc_vec P [a; b; c] s | _ => pp_raise "shen-jit.absvector3" end.
Definition pp_filled_vector : pp_rule := fun P args s => match args with
 | [VNum (NInt n); x] =>
   if (Z.ltb n 0 || Z.leb 281474976710656 n)%bool then pp_raise "shen-jit.filled-vector: not a valid length"
   else alloc_vec P (repeat x (Z.to_nat n)) s
 | _ => pp_raise "shen-jit.filled-vector: not a valid length" end.
Definition pp_taggedp : pp_rule := fun _ args s => match args with
 | [VVec l; b] => match cells s l with x :: _ => pp_identity (pp_same x b) s | [] => pp_bool false s end
 | _ => pp_bool false s end.
Definition pp_vectorp : pp_rule := fun _ args s => match args with
 | [VVec l] => match cells s l with
   | VNum (NInt z) :: _ => pp_bool (Z.leb 0 z) s
   | VNum (NFloat r) :: _ => pp_bool (JitFloat.JitFloat.ge r 0) s
   | _ => pp_bool false s end
 | _ => pp_bool false s end.
Definition pp_symbol_kind : pp_rule := fun _ args s => match args with
 | [VSym x] => ret (VNum (NInt (JitBytecode.JitBytecode.name_kind x))) s
 | _ => ret (VNum (NInt 0)) s end.
Definition pp_samep : pp_rule := fun _ args s => match args with
 | [a; b] => pp_identity (pp_same a b) s | _ => pp_raise "shen-jit.same?" end.
(* 0.6 has no character streams: char-stream? is false, and both others raise (prims.c). *)
Definition pp_char_streamp : pp_rule := fun _ _ s => pp_bool false s.
Definition pp_no_char_streams : pp_rule := fun _ _ _ => pp_raise "character streams are not supported".
Definition pp_hash (hash : list (list value) -> value -> Z) : pp_rule := fun _ args s => match args with
 | [a; VNum (NInt n)] =>
   if Z.leb n 0 then pp_raise "hash: not a valid bound"
   else let h := Z.rem (hash (heap s) a) n in ret (VNum (NInt (if Z.eqb h 0 then 1 else h))) s
 | _ => pp_raise "hash: not a valid bound" end.
(* shen-jit.decimal S E: the decimal S, with its own exponent if it has one, times 10^E. *)
Definition decimal_split (x : list N) : list N * Z :=
 (fix split (l acc : list N) : list N * Z := match l with
   | 101%N :: r =>
     let '(neg, ds) := match r with 45%N :: q => (true, q) | 43%N :: q => (false, q) | _ => (false, r) end in
     let '(v, _, _) := JitFloat.JitFloat.scan_digits ds 0 0 in (rev acc, if neg then (- v)%Z else v)
   | c :: r => split r (c :: acc)
   | [] => (rev acc, 0%Z) end) x [].
Definition pp_decimal : pp_rule := fun _ args s => match args with
 | [VStr x; VNum (NInt ex)] => let '(mant, own) := decimal_split x in
   ret (VNum (NFloat (JitFloat.JitFloat.parse_decimal mant (ex + own)))) s
 | _ => pp_raise "shen-jit.decimal: not a string and an exponent" end.

(* Dictionaries (dict.c): a vector [tag; count; buckets], the buckets a vector of a nonzero power
   of two of association lists, the bucket the hash's low bits. *)
Definition dict_parts (s : store) (d : value) : option (nat * value * Z * nat * list value) :=
 match d with
 | VVec l => match cells s l with
   | [tag; VNum (NInt n); VVec b] =>
     if Z.ltb n 0 then None else
     let bs := cells s b in
     let len := N.of_nat (List.length bs) in
     if andb (N.ltb 0 len) (N.eqb (N.land len (len - 1)) 0) then Some (l, tag, n, b, bs) else None
   | _ => None end
 | _ => None end.
Definition bucket_index (hash : list (list value) -> value -> Z) (s : store) (k : value) (len : nat) : nat :=
 Z.to_nat (Z.land (hash (heap s) k) (Z.of_nat len - 1)).
Fixpoint bucket_find (eq : value -> value -> option bool) (k c : value) : option (option (value * value)) :=
 match c with
 | VNil => Some None
 | VCons (VCons kk vv) r => match eq kk k with
   | Some true => Some (Some (kk, vv)) | Some false => bucket_find eq k r | None => None end
 | _ => None end.
Definition not_dict : presult := pp_raise "not a dictionary".

Definition pp_dict_find hash : pp_rule := fun P args s => match args with
 | [dv; k] => match dict_parts s dv with
   | None => not_dict
   | Some (_, _, _, _, bs) => match nth_error bs (bucket_index hash s k (List.length bs)) with
     | Some c => match bucket_find (pp_eq P s) k c with
       | Some (Some (kk, vv)) => ret (VCons kk vv) s
       | Some None => ret VNil s
       | None => not_dict end
     | None => not_dict end end
 | _ => not_dict end.

Definition pp_dict_put hash : pp_rule := fun P args s => match args with
 | [dv; k; v] => match dict_parts s dv with
   | None => not_dict
   | Some (l, tag, n, b, bs) =>
     let eq := pp_eq P s in
     let i := bucket_index hash s k (List.length bs) in
     let c := nth i bs VNil in
     let fix put_in (c : value) : value := match c with
       | VCons (VCons kk vv) r => match eq kk k with
         | Some true => VCons (VCons kk v) r | _ => VCons (VCons kk vv) (put_in r) end
       | x => x end in
     match bucket_find eq k c with
     | None => not_dict
     | Some (Some _) => ret v (put_cells s b (replace_nth i (put_in c) bs))
     | Some None =>
       let s1 := put_cells s b (replace_nth i (VCons (VCons k v) c) bs) in
       let n' := (n + 1)%Z in
       if Z.ltb (Z.of_nat (List.length bs)) n' then
         (* grow: double, relinking each bucket from its head (dict.c, grow) *)
         let len := (2 * List.length bs)%nat in
         let fresh := fold_left (fun acc cl =>
           let fix go (cl : value) (acc : list value) : list value := match cl with
             | VCons (VCons kk vv) r =>
               let j := bucket_index hash s kk len in
               go r (replace_nth j (VCons (VCons kk vv) (nth j acc VNil)) acc)
             | _ => acc end in
           go cl acc) (cells s1 b) (repeat VNil len) in
         if alloc_ok P (heap s1) len then
           let nb := List.length (heap s1) in
           let s2 := Store (heap s1 ++ [fresh]) (gvals s1) (gfuns s1) in
           ret v (put_cells s2 l [tag; VNum (NInt n'); VVec nb])
         else PDone (OFail Observation.Observation.RHeap)
       else ret v (put_cells s1 l [tag; VNum (NInt n'); VVec b]) end end
 | _ => not_dict end.

Definition pp_dict_remove hash : pp_rule := fun P args s => match args with
 | [dv; k] => match dict_parts s dv with
   | None => not_dict
   | Some (l, tag, n, b, bs) =>
     let eq := pp_eq P s in
     let i := bucket_index hash s k (List.length bs) in
     let c := nth i bs VNil in
     let fix rm (c : value) : value := match c with
       | VCons (VCons kk vv) r => match eq kk k with
         | Some true => r | _ => VCons (VCons kk vv) (rm r) end
       | x => x end in
     match bucket_find eq k c with
     | None => not_dict
     | Some None => ret k s
     | Some (Some _) =>
       ret k (put_cells (put_cells s b (replace_nth i (rm c) bs)) l [tag; VNum (NInt (n - 1)); VVec b]) end end
 | _ => not_dict end.

Definition pp_dict_entries : pp_rule := fun _ args s => match args with
 | [dv] => match dict_parts s dv with
   | None => not_dict
   | Some (_, _, _, _, bs) =>
     let fix walk (c acc : value) : value := match c with
       | VCons (VCons kk vv) r => walk r (VCons (VCons kk vv) acc) | _ => acc end in
     ret (fold_left (fun acc c => walk c acc) bs VNil) s end
 | _ => not_dict end.

(* The table: name, arity (prim_table's), rule. The core needs no parameter; the hash and the
   three dictionary operators that hash a key read the environment's hash. *)
Definition jit_port_prim_core_table : list (string * nat * pp_rule) :=
 [("shen-jit.symbol?", 1%nat, pp_symbolp); ("shen-jit.integer?", 1%nat, pp_integerp);
  ("shen-jit.append", 2%nat, pp_append); ("shen-jit.absvector3", 3%nat, pp_absvector3);
  ("shen-jit.filled-vector", 2%nat, pp_filled_vector); ("shen-jit.tagged?", 2%nat, pp_taggedp);
  ("shen-jit.vector?", 1%nat, pp_vectorp); ("shen-jit.symbol-kind", 1%nat, pp_symbol_kind);
  ("shen-jit.same?", 2%nat, pp_samep); ("char-stream?", 1%nat, pp_char_streamp);
  ("read-unit-string", 1%nat, pp_no_char_streams); ("write-string", 2%nat, pp_no_char_streams);
  ("shen-jit.decimal", 2%nat, pp_decimal); ("shen-jit.dict-entries", 1%nat, pp_dict_entries)].
Definition jit_port_prim_hash_table (hash : list (list value) -> value -> Z) : list (string * nat * pp_rule) :=
 [("shen-jit.hash", 2%nat, pp_hash hash);
  ("shen-jit.dict-find", 2%nat, pp_dict_find hash); ("shen-jit.dict-put", 3%nat, pp_dict_put hash);
  ("shen-jit.dict-remove", 2%nat, pp_dict_remove hash)].
Definition jit_port_prim_table (hash : list (list value) -> value -> Z) : list (string * nat * pp_rule) :=
 jit_port_prim_core_table ++ jit_port_prim_hash_table hash.

Definition pp_lookup (t : list (string * nat * pp_rule)) (f : name) : option (nat * pp_rule) :=
 match find (fun e => match e with (nm, _, _) => text_eqb f (of_string nm) end) t with
 | Some (_, n, r) => Some (n, r) | None => None end.
(* The whole proposal, and the 14 operators of it that need no hash: either can be wired in. *)
Definition jit_port_prims_proposed (hash : list (list value) -> value -> Z) : name -> option (nat * pp_rule) :=
 pp_lookup (jit_port_prim_table hash).
Definition jit_port_prims_core : name -> option (nat * pp_rule) := pp_lookup jit_port_prim_core_table.

(* No candidate, with the reason. *)
Definition jit_port_prims_residual : list (string * string) :=
 [("shen-jit.write-bytes", "byte buffers: KL has no value for one (a vector fails absvector?, a string string?)");
  ("shen-jit.string->bytes", "byte buffers"); ("shen-jit.bytes-length", "byte buffers"); ("shen-jit.u8", "byte buffers");
  ("shen-jit.pvar", "Prolog variables: KL has no value for one"); ("shen-jit.pvar?", "Prolog variables");
  ("shen-jit.pvar-offset", "Prolog variables"); ("shen-jit.deref", "Prolog variables");
  ("shen-jit.read-file", "one request for a whole file: KL's requests are open, read and close");
  ("shen-jit.exit", "an exit status: KL has no such outcome");
  ("shen-jit.quiet?", "reads the bytecode's handler stack"); ("shen-jit.mark-toplevel", "excluded in JitBytecode (is_excluded)");
  ("shen-jit.trace-text", "excluded in JitBytecode (is_excluded)");
  ("shen-jit.install", "reads and makes code objects"); ("shen-jit.inline-body", "reads a code object");
  ("shen-jit.sealed?", "reads the image's sealed set (OB-JIT-IMAGE)"); ("shen-jit.sealing", "sets the image's sealing flag");
  ("shen-jit.inlined?", "reads a code object (0 uses at v0.6: stage 0 seals every input)");
  ("shen-jit.arity?", "reads a code object (0 uses at v0.6)")].

(* Census, not evidence: the operators found, by a walk of the 955 v0.6 witnesses (norm witness set
   sha256 e45add98...b69dd1), that are neither KL primitives nor raise-cond. *)
Definition port_prims_census : list string :=
 ["char-stream?"; "read-unit-string"; "shen-jit.absvector3"; "shen-jit.append"; "shen-jit.bytes-length";
  "shen-jit.decimal"; "shen-jit.deref"; "shen-jit.dict-entries"; "shen-jit.dict-find"; "shen-jit.dict-put";
  "shen-jit.dict-remove"; "shen-jit.exit"; "shen-jit.filled-vector"; "shen-jit.hash"; "shen-jit.inline-body";
  "shen-jit.install"; "shen-jit.integer?"; "shen-jit.mark-toplevel"; "shen-jit.pvar"; "shen-jit.pvar-offset";
  "shen-jit.pvar?"; "shen-jit.quiet?"; "shen-jit.read-file"; "shen-jit.same?"; "shen-jit.sealed?";
  "shen-jit.sealing"; "shen-jit.string->bytes"; "shen-jit.symbol-kind"; "shen-jit.symbol?"; "shen-jit.tagged?";
  "shen-jit.trace-text"; "shen-jit.u8"; "shen-jit.vector?"; "shen-jit.write-bytes"; "write-string"].

Definition jit_rules (sealed : list name) : port_rules := PortRules
 (Some (JitBytecode.JitBytecode.fix_min, JitBytecode.JitBytecode.fix_max))
 jit_char_text
 true
 true
 (fun _ f => negb (is_fixed_name f || existsb (text_eqb f) sealed))
 (fun k => orb (text_eqb k (of_string "run")) (text_eqb k (of_string "unix")))
 false (* 0.4: write-byte and close raise on a failed write (tizoc/shen-jit#12), as the agreed rule does *)
 (fun r => match r with
  | Observation.Observation.RHeap => Some (XUser (of_string "out of memory"))
  | Observation.Observation.RStack => Some (XUser (of_string "stack overflow")) end)
 (fun _ => None) (* port primitives: none until Reuben decides on jit_port_prims_proposed (OB-JIT-PORT-PRIMS) *).

Definition fix_max_val : Z := JitBytecode.JitBytecode.fix_max.

(* A result past the fixnum range raises. *)
Theorem jit_overflow_raises : forall sealed s,
 rule_arith_r (jit_rules sealed) jit_profile PAdd Z.add [VNum (NInt fix_max_val); VNum (NInt 1)] s = dom PAdd.
Proof. intros. apply range_raises. vm_compute. reflexivity. Qed.

(* Comparison does not round: 2^53 + 1 is above the real 2^53, which a double conversion would not see. *)
Theorem jit_compare_exact :
 jit_inexact_cmp PGt (NInt 9007199254740993) (NFloat (JitFloat.JitFloat.of_Z 9007199254740992)) = true /\
 jit_inexact_cmp PEqual (NInt 9007199254740993) (NFloat (JitFloat.JitFloat.of_Z 9007199254740992)) = false.
Proof. split; vm_compute; reflexivity. Qed.

(* Strings are bytes. From 0.6, n->string makes one byte of 0 to 255 and the UTF-8 bytes of any
   other Unicode scalar value; a surrogate, a negative number or one past U+10FFFF raises. *)
Theorem jit_byte_strings : forall sealed s,
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 255)] s = ret (VStr [255%N]) s /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 256)] s = ret (VStr [196%N; 128%N]) s /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 955)] s = ret (VStr [206%N; 187%N]) s /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 8364)] s = ret (VStr [226%N; 130%N; 172%N]) s /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 128512)] s = ret (VStr [240%N; 159%N; 152%N; 128%N]) s /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 55296)] s = dom PNToString /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 1114112)] s = dom PNToString /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt (-1))] s = dom PNToString.
Proof. intros. repeat split; reflexivity. Qed.

(* The profile's n->string is the bytecode's: each integer the one accepts, the other turns into
   the same bytes, and each one rejects, the other rejects. *)
Theorem jit_n_to_string_agrees : forall z,
 jit_char_text z = JitBytecode.JitBytecode.utf8_of z.
Proof. reflexivity. Qed.

(* From 0.4, a failed write raises (tizoc/shen-jit#12), so write-byte follows the agreed rule. *)
Theorem jit_writes_checked : forall sealed args s,
 rule_write_byte_r (jit_rules sealed) args s = rule_write_byte args s.
Proof. reflexivity. Qed.

(* A named call of the wrong count raises, and a resource failure can be caught. *)
Theorem jit_no_partial : forall sealed g args k s ps b,
 lookup g (gfuns s) = Some (FUser ps b) -> List.length args <> List.length ps ->
 call_named_r (jit_rules sealed) jit_profile g args k s = MTau (Cfg (Throw XArity) k s).
Proof. intros. eapply no_partial_application; [reflexivity|eassumption|assumption]. Qed.

Theorem jit_resources_catchable : forall sealed k s,
 next_r (jit_rules sealed) jit_profile (Cfg (Fail Observation.Observation.RStack) k s)
 = MTau (Cfg (Throw (XUser (of_string "stack overflow"))) k s).
Proof. intros. apply catchable_resource. reflexivity. Qed.

(* defun of a primitive's name or a sealed name is refused. *)
Theorem jit_defun_fixed_refused : forall sealed rho ps b k s,
 eval_move_r (jit_rules sealed) jit_profile rho (EDefun (of_string "hd") ps b) k s
 = MTau (Cfg (Throw XBadDefinition) k s).
Proof. intros. apply defun_refused. reflexivity. Qed.

Theorem jit_defun_sealed_refused : forall sealed f rho ps b k s,
 existsb (text_eqb f) sealed = true ->
 eval_move_r (jit_rules sealed) jit_profile rho (EDefun f ps b) k s
 = MTau (Cfg (Throw XBadDefinition) k s).
Proof.
 intros sealed f rho ps b k s H. apply defun_refused. cbn [defun_allowed jit_rules]. rewrite H.
 rewrite orb_true_r. reflexivity.
Qed.

(* --- sanity: what the port-primitive proposal says --- *)
Definition pcall hash (nm : string) (P : profile) (args : list value) (s : store) : option presult :=
 match jit_port_prims_proposed hash (of_string nm) with Some (_, r) => Some (r P args s) | None => None end.
Definition sym (x : string) : value := VSym (of_string x).
Definition hash0 : list (list value) -> value -> Z := fun _ _ => 0%Z.

(* Every operator of the census, and inlined? and arity?, has a candidate or a named reason, not both. *)
Theorem jit_port_prims_partition : forall hash,
 forallb (fun nm => xorb (match jit_port_prims_proposed hash (of_string nm) with Some _ => true | None => false end)
                         (existsb (String.eqb nm) (map fst jit_port_prims_residual)))
   (port_prims_census ++ ["shen-jit.inlined?"; "shen-jit.arity?"]) = true.
Proof. intros. reflexivity. Qed.

(* Each candidate is a primitive of the bytecode's table, at its arity there, and none is a KL primitive. *)
Theorem jit_port_prims_arity : forall hash,
 forallb (fun e => match e with (nm, n, _) =>
   existsb (fun p => match p with (nm', _, a) => String.eqb nm nm' && Nat.eqb a n end) JitBytecode.JitBytecode.prim_table
   && negb (existsb (fun p => String.eqb nm (prim_name p)) all_prims) end) (jit_port_prim_table hash) = true.
Proof. intros. reflexivity. Qed.

(* The gate: jit_rules has no port primitive, so each of these still raises XUndefinedFun. *)
Theorem jit_port_prims_off : forall sealed g, port_prim (jit_rules sealed) g = None.
Proof. reflexivity. Qed.

Theorem pp_symbolp_ok : forall h s,
 pcall h "shen-jit.symbol?" jit_profile [sym "a"] s = Some (ret (VBool true) s) /\
 pcall h "shen-jit.symbol?" jit_profile [VBool true] s = Some (ret (VBool false) s).
Proof. split; reflexivity. Qed.

(* 3, and the double 3.0, are integers; the double 0.5 is not. *)
Theorem pp_integerp_ok : forall h s,
 pcall h "shen-jit.integer?" jit_profile [VNum (NInt 3)] s = Some (ret (VBool true) s) /\
 pcall h "shen-jit.integer?" jit_profile [VNum (NFloat 4613937818241073152)] s = Some (ret (VBool true) s) /\
 pcall h "shen-jit.integer?" jit_profile [VNum (NFloat 4602678819172646912)] s = Some (ret (VBool false) s).
Proof. intros. repeat split; vm_compute; reflexivity. Qed.

Theorem pp_append_ok : forall h s,
 pcall h "shen-jit.append" jit_profile [VCons (VNum (NInt 1)) (VCons (VNum (NInt 2)) VNil); VCons (VNum (NInt 3)) VNil] s
 = Some (ret (VCons (VNum (NInt 1)) (VCons (VNum (NInt 2)) (VCons (VNum (NInt 3)) VNil))) s) /\
 pcall h "shen-jit.append" jit_profile [VNum (NInt 1); VNil] s = Some (pp_raise "attempt to append a non-list").
Proof. split; reflexivity. Qed.

Theorem pp_absvector3_ok : forall h a b c s,
 pcall h "shen-jit.absvector3" jit_profile [a; b; c] s
 = Some (ret (VVec (List.length (heap s))) (Store (heap s ++ [[a; b; c]]) (gvals s) (gfuns s))).
Proof. reflexivity. Qed.

Theorem pp_filled_vector_ok : forall h x s,
 pcall h "shen-jit.filled-vector" jit_profile [VNum (NInt 2); x] s
 = Some (ret (VVec (List.length (heap s))) (Store (heap s ++ [[x; x]]) (gvals s) (gfuns s))) /\
 pcall h "shen-jit.filled-vector" jit_profile [VNum (NInt (-1)); x] s = Some (pp_raise "shen-jit.filled-vector: not a valid length").
Proof. split; reflexivity. Qed.

Definition s_tag : store := Store [[sym "tuple"; VNil]; [VNum (NInt 3)]; [VCons VNil VNil]] [] [].
Theorem pp_taggedp_ok : forall h,
 pcall h "shen-jit.tagged?" jit_profile [VVec 0; sym "tuple"] s_tag = Some (ret (VBool true) s_tag) /\
 pcall h "shen-jit.tagged?" jit_profile [VVec 0; sym "vector"] s_tag = Some (ret (VBool false) s_tag) /\
 pcall h "shen-jit.tagged?" jit_profile [VNil; sym "tuple"] s_tag = Some (ret (VBool false) s_tag) /\
 pcall h "shen-jit.tagged?" jit_profile [VVec 2; VCons VNil VNil] s_tag = Some (PDone (OWrong (of_string "identity-undefined"))).
Proof. repeat split; reflexivity. Qed.

Theorem pp_vectorp_ok : forall h,
 pcall h "shen-jit.vector?" jit_profile [VVec 1] s_tag = Some (ret (VBool true) s_tag) /\
 pcall h "shen-jit.vector?" jit_profile [VVec 0] s_tag = Some (ret (VBool false) s_tag) /\
 pcall h "shen-jit.vector?" jit_profile [sym "a"] s_tag = Some (ret (VBool false) s_tag).
Proof. repeat split; reflexivity. Qed.

(* X is a variable (2), foo a symbol (1), 12 or a non-symbol neither (0). *)
Theorem pp_symbol_kind_ok : forall h s,
 pcall h "shen-jit.symbol-kind" jit_profile [sym "X"] s = Some (ret (VNum (NInt 2)) s) /\
 pcall h "shen-jit.symbol-kind" jit_profile [sym "foo"] s = Some (ret (VNum (NInt 1)) s) /\
 pcall h "shen-jit.symbol-kind" jit_profile [sym "12"] s = Some (ret (VNum (NInt 0)) s) /\
 pcall h "shen-jit.symbol-kind" jit_profile [VStr (of_string "X")] s = Some (ret (VNum (NInt 0)) s).
Proof. intros. repeat split; vm_compute; reflexivity. Qed.

Theorem pp_samep_ok : forall h s,
 pcall h "shen-jit.same?" jit_profile [sym "a"; sym "a"] s = Some (ret (VBool true) s) /\
 pcall h "shen-jit.same?" jit_profile [VVec 0; VVec 1] s = Some (ret (VBool false) s) /\
 pcall h "shen-jit.same?" jit_profile [VNum (NInt 1); sym "a"] s = Some (ret (VBool false) s) /\
 pcall h "shen-jit.same?" jit_profile [VStr []; VStr []] s = Some (PDone (OWrong (of_string "identity-undefined"))).
Proof. repeat split; reflexivity. Qed.

Theorem pp_char_streams_ok : forall h v w s,
 pcall h "char-stream?" jit_profile [v] s = Some (ret (VBool false) s) /\
 pcall h "read-unit-string" jit_profile [v] s = Some (pp_raise "character streams are not supported") /\
 pcall h "write-string" jit_profile [v; w] s = Some (pp_raise "character streams are not supported").
Proof. repeat split; reflexivity. Qed.

(* The hash's remainder by the bound, 0 read as 1; a bound below 1 raises. *)
Theorem pp_hash_ok : forall h a s,
 h (heap s) a = 7%Z ->
 pcall h "shen-jit.hash" jit_profile [a; VNum (NInt 5)] s = Some (ret (VNum (NInt 2)) s) /\
 pcall h "shen-jit.hash" jit_profile [a; VNum (NInt 7)] s = Some (ret (VNum (NInt 1)) s) /\
 pcall h "shen-jit.hash" jit_profile [a; VNum (NInt 0)] s = Some (pp_raise "hash: not a valid bound").
Proof. intros h a s H. repeat split; unfold pcall, jit_port_prims_proposed, pp_hash; simpl; rewrite H; reflexivity. Qed.

(* "15" at 10^1 and "1.5e2" at 10^0 are both the double 150. *)
Theorem pp_decimal_ok : forall h s,
 pcall h "shen-jit.decimal" jit_profile [VStr (of_string "15"); VNum (NInt 1)] s
 = Some (ret (VNum (NFloat (JitFloat.JitFloat.of_Z 150))) s) /\
 pcall h "shen-jit.decimal" jit_profile [VStr (of_string "1.5e2"); VNum (NInt 0)] s
 = Some (ret (VNum (NFloat (JitFloat.JitFloat.of_Z 150))) s).
Proof. intros. split; vm_compute; reflexivity. Qed.

(* A dictionary of one bucket: put a new key, put it again, find, remove, list, and a second key
   that doubles the buckets (with every key hashed to 0). *)
Definition d0 : store := Store [[sym "dict"; VNum (NInt 0); VVec 1]; [VNil]] [] [].
Definition d1 : store := Store [[sym "dict"; VNum (NInt 1); VVec 1]; [VCons (VCons (sym "a") (VNum (NInt 1))) VNil]] [] [].
Definition d1' : store := Store [[sym "dict"; VNum (NInt 1); VVec 1]; [VCons (VCons (sym "a") (VNum (NInt 9))) VNil]] [] [].
Definition d2 : store := Store
 [[sym "dict"; VNum (NInt 2); VVec 2];
  [VCons (VCons (sym "b") (VNum (NInt 2))) (VCons (VCons (sym "a") (VNum (NInt 1))) VNil)];
  [VCons (VCons (sym "a") (VNum (NInt 1))) (VCons (VCons (sym "b") (VNum (NInt 2))) VNil); VNil]] [] [].
Definition d1_removed : store := Store [[sym "dict"; VNum (NInt 0); VVec 1]; [VNil]] [] [].

Theorem pp_dict_ok :
 pcall hash0 "shen-jit.dict-find" jit_profile [VVec 0; sym "a"] d0 = Some (ret VNil d0) /\
 pcall hash0 "shen-jit.dict-put" jit_profile [VVec 0; sym "a"; VNum (NInt 1)] d0 = Some (ret (VNum (NInt 1)) d1) /\
 pcall hash0 "shen-jit.dict-put" jit_profile [VVec 0; sym "a"; VNum (NInt 9)] d1 = Some (ret (VNum (NInt 9)) d1') /\
 pcall hash0 "shen-jit.dict-find" jit_profile [VVec 0; sym "a"] d1 = Some (ret (VCons (sym "a") (VNum (NInt 1))) d1) /\
 pcall hash0 "shen-jit.dict-remove" jit_profile [VVec 0; sym "a"] d1 = Some (ret (sym "a") d1_removed) /\
 pcall hash0 "shen-jit.dict-remove" jit_profile [VVec 0; sym "z"] d1 = Some (ret (sym "z") d1) /\
 pcall hash0 "shen-jit.dict-entries" jit_profile [VVec 0] d1 = Some (ret (VCons (VCons (sym "a") (VNum (NInt 1))) VNil) d1) /\
 pcall hash0 "shen-jit.dict-put" jit_profile [VVec 0; sym "b"; VNum (NInt 2)] d1 = Some (ret (VNum (NInt 2)) d2) /\
 pcall hash0 "shen-jit.dict-find" jit_profile [VNil; sym "a"] d1 = Some (pp_raise "not a dictionary").
Proof. repeat split; vm_compute; reflexivity. Qed.

(* --- The deviation table --- *)
Inductive disposition :=
 | In_profile              (* a profile slot expresses it *)
 | In_port_rules           (* KLPort.port_rules states it, in jit_rules *)
 | In_bytecode             (* JitBytecode.v states it; the KLambda profile does not need it *)
 | Partly_stated           (* stated in part: the entry's ledger item has the rest *)
 | Ledger_only.            (* tracked; no rule states it *)

Record deviation := Dev { d_id : string; d_rule : string; d_where : disposition; d_ledger : string }.

Definition deviations : list deviation :=
 [Dev "fixnum-overflow" "integers are 62-bit; a result out of range raises integer overflow (semantics.md s3)"
    In_port_rules "OB-JIT-DEV-FIXNUM";
  Dev "ieee-doubles" "reals are binary64; mixed arithmetic gives a real" In_profile "OB-JIT-FLOAT-MODEL";
  Dev "division" "integer division exact or real; any zero divisor raises" In_profile "OB-JIT-DEV-DIVISION";
  Dev "mixed-equality" "= and comparisons across integers and reals are exact (s3); #2 fixed at this pin" In_profile "OB-JIT-ISSUE-2";
  Dev "nan-identity" "a NaN is = to itself as one object and to nothing else" In_bytecode "OB-JIT-NAN-IDENTITY";
  Dev "literals" "reader overrides make out-of-range literals reals (s3)" Ledger_only "OB-JIT-DEV-LITERALS";
  Dev "printing" "reals print shortest round-trip digits (s3)" In_profile "OB-JIT-DEV-PRINTING";
  Dev "byte-strings" "strings are bytes; n->string makes one byte of 0 to 255 and UTF-8 of other scalar values (s4, 0.6)" In_port_rules "OB-JIT-DEV-BYTES";
  Dev "hash" "hash is consistent with = and hashes 8 and 8.0 alike (s6)" In_bytecode "OB-JIT-DEV-HASH";
  Dev "closure-equality" "closures and streams compare by identity; two exceptions stay undefined here (s6)" Partly_stated "OB-JIT-DEV-IDENTITY";
  Dev "error-to-string" "error-to-string of a non-exception raises (s8)" In_bytecode "OB-JIT-DEV-ETS";
  Dev "cond-no-clause" "cond with no true clause raises (s9)" In_profile "OB-JIT-DEV-COND";
  Dev "no-partial" "a named call of the wrong arity raises; there is no partial application (s9)"
    In_port_rules "OB-JIT-DEV-ARITY";
  Dev "symbols-not-procedures" "applying a symbol raises (s9)" In_bytecode "OB-JIT-DEV-APPLY";
  Dev "defun-validation" "malformed defun raises at definition (s10)" Ledger_only "OB-JIT-DEV-DEFUN";
  Dev "fixed-names" "defun of a fixed name raises (s10)" In_port_rules "OB-JIT-DEV-SEALING";
  Dev "sealing" "defun of a sealed name raises; sealed calls bind once (s10)" In_port_rules "OB-JIT-DEV-SEALING";
  Dev "lazy-lambda-form" "lambda forms are made on first fn; a placeholder before that (s11)" Ledger_only "OB-JIT-DEV-LAZY-FORM";
  Dev "get-time" "get-time takes run and unix only, and returns reals (s12)" In_port_rules "OB-JIT-DEV-TIME";
  Dev "char-streams" "char-stream? is false; read-unit-string and write-string raise (s12)" In_bytecode "OB-JIT-DEV-CHAR";
  Dev "catchable-resources" "stack overflow and out of memory are catchable errors (s14)"
    In_port_rules "OB-JIT-DEV-RESOURCES";
  Dev "cyclic-equality" "= on a cycle, or past its budgets, ends the process; #3's deep-term crash is fixed (s6)" Ledger_only "OB-JIT-ISSUE-3"].

End JitProfile.
