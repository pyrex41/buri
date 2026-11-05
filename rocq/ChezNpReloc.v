(* E2E-22: np-generate-code output against the exact tarm64le code bytes.

   np-generate-code (cpnanopass.ss) ends Chez's nanopass pipeline with a
   $c-func record whose code-list is a sequence of assembler entries.
   compile.ss c-mkcode (lines 102-190) lays them out from offset
   code-data-disp: (long . n) writes 4 little-endian bytes, (quad . n) 8,
   (code-top-link) the 8-byte value of the current offset, and
   (arm64-abs|arm64-call|arm64-jump n target) writes nothing but registers a
   relocation for the preceding movz/movk/movk/movk (16 bytes, abs) or
   movz/movk/movk/movk/branch (20 bytes, call/jump) window.  When the code
   object is installed, c/fasl.c arm64_set_abs (lines 1714-1735) rewrites the
   four move words with the 64-bit target address, keeping the destination
   register of the fourth word.

   [check_code_object] accepts a template (the printed code-list) and the
   captured bytes only when the captured bytes are exactly the template with
   every relocation window rewritten by arm64_set_abs for some 64-bit item,
   each template window holds arm64_set_abs of item 0, and the relocation
   offsets and targets equal the code object's own relocation table.  Every
   other byte must be identical.  Entries it does not model make it reject. *)
From Coq Require Import String Ascii List Bool Arith ZArith.
From Buri Require Import ChezNpReader ChezNpCore.
Import ListNotations.
Open Scope string_scope.

Fixpoint digits_Z_acc (acc : Z) (s : string) : Z :=
  match s with
  | EmptyString => acc
  | String c r => digits_Z_acc (acc * 10 + Z.of_nat (nat_of_ascii c - 48))%Z r
  end.

Definition z_of_atom (x : sexp) : option Z :=
  match x with
  | Atom (String c r as a) =>
      if is c 45 then
        if andb (negb (String.eqb r "")) (all_digits r) then Some (- digits_Z_acc 0 r)%Z else None
      else if all_digits a then Some (digits_Z_acc 0 a) else None
  | _ => None
  end.

Definition le_bytes (n : nat) (v : Z) : list Z :=
  map (fun j => Z.land (Z.shiftr v (8 * Z.of_nat j)) 255) (seq 0 n).

Inductive reloc_kind := RAbs | RCall | RJump.

Record reloc : Type := mkReloc {
  r_kind : reloc_kind;
  r_offset : nat;       (* first byte of the move window, from code start *)
  r_disp : Z;           (* the entry's n: added to the target address *)
  r_target : sexp
}.

Definition code_data_disp : Z := 65.

Definition head_is (x : sexp) (k : string) : bool :=
  match x with
  | Lst (Atom a :: _) => String.eqb a k
  | Dot [Atom a] _ => String.eqb a k
  | _ => false
  end.

(* Lay out entries; [pos] is the number of bytes emitted so far. *)
Fixpoint layout (pos : nat) (es : list sexp) : option (list Z * list reloc) :=
  match es with
  | [] => Some ([], [])
  | e :: r =>
      match e with
      | Dot [Atom k] v =>
          match z_of_atom v with
          | Some n =>
              if String.eqb k "long" then
                if andb (Z.leb 0 n) (Z.ltb n (2 ^ 32)) then
                  match layout (pos + 4) r with
                  | Some (bs, rs) => Some (app (le_bytes 4 n) bs, rs)
                  | None => None
                  end
                else None
              else if String.eqb k "quad" then
                if andb (Z.leb 0 n) (Z.ltb n (2 ^ 64)) then
                  match layout (pos + 8) r with
                  | Some (bs, rs) => Some (app (le_bytes 8 n) bs, rs)
                  | None => None
                  end
                else None
              else None
          | None => None
          end
      | Lst [Atom k] =>
          if String.eqb k "code-top-link" then
            match layout (pos + 8) r with
            | Some (bs, rs) => Some (app (le_bytes 8 (code_data_disp + Z.of_nat pos)%Z) bs, rs)
            | None => None
            end
          else None
      | Lst [Atom k; n; target] =>
          let mk kind width :=
            match z_of_atom n with
            | Some d =>
                if Nat.leb width pos then
                  match layout pos r with
                  | Some (bs, rs) => Some (bs, mkReloc kind (pos - width) d target :: rs)
                  | None => None
                  end
                else None
            | None => None
            end in
          if String.eqb k "arm64-abs" then mk RAbs 16%nat
          else if String.eqb k "arm64-call" then mk RCall 20%nat
          else if String.eqb k "arm64-jump" then mk RJump 20%nat
          else None
      | _ => None
      end
  end.

(* ---- arm64_set_abs / arm64_get_abs (c/fasl.c) ---------------------------- *)

Definition movz_opcode : Z := 3531603968.   (* 0xD2800000 *)
Definition movk_opcode : Z := 4068474880.   (* 0xF2800000 *)
Definition address_bits_mask : Z := 2097120. (* 0x1fffe0 *)

Definition set_abs_word (k : nat) (dest item : Z) : Z :=
  Z.lor (Z.lor (Z.lor (if Nat.eqb k 0 then movz_opcode else movk_opcode)
                      (Z.shiftl (Z.of_nat k) 21))
               dest)
        (Z.shiftl (Z.land (Z.shiftr item (16 * Z.of_nat k)) 65535) 5).

Definition set_abs_bytes (dest item : Z) : list Z :=
  flat_map (fun k => le_bytes 4 (set_abs_word k dest item)) (seq 0 4).

Definition word_at (bs : list Z) (off : nat) : Z :=
  fold_right (fun j acc => Z.lor acc (Z.shiftl (nth (off + j) bs 0%Z) (8 * Z.of_nat j)))
             0%Z (seq 0 4).

Definition get_abs (bs : list Z) (off : nat) : Z :=
  fold_right (fun k acc =>
      Z.lor acc (Z.shiftl (Z.shiftr (Z.land (word_at bs (off + 4 * k)) address_bits_mask) 5)
                          (16 * Z.of_nat k)))
    0%Z (seq 0 4).

Definition dest_reg (bs : list Z) (off : nat) : Z := Z.land (word_at bs (off + 12)) 31.

Fixpoint overwrite (bs : list Z) (off : nat) (new : list Z) : list Z :=
  match bs with
  | [] => []
  | b :: r =>
      match off with
      | O => match new with [] => bs | n :: nr => n :: overwrite r O nr end
      | S o => b :: overwrite r o new
      end
  end.

(* The relocation instance of a template: each window rewritten with its
   item, keeping the template's destination register. *)
Fixpoint instantiate (tmpl : list Z) (rs : list reloc) (items : list Z) : list Z :=
  match rs, items with
  | r :: rr, i :: ir =>
      instantiate (overwrite tmpl (r_offset r) (set_abs_bytes (dest_reg tmpl (r_offset r)) i)) rr ir
  | _, _ => tmpl
  end.

Definition items_of (captured : list Z) (rs : list reloc) : list Z :=
  map (fun r => get_abs captured (r_offset r)) rs.

Definition window (bs : list Z) (off : nat) : list Z := firstn 16 (skipn off bs).

Definition zlist_eqb (a b : list Z) : bool :=
  if list_eq_dec Z.eq_dec a b then true else false.

Definition template_windows_zero (tmpl : list Z) (rs : list reloc) : bool :=
  forallb (fun r => zlist_eqb (window tmpl (r_offset r))
                              (set_abs_bytes (dest_reg tmpl (r_offset r)) 0%Z)) rs.

Definition windows_disjoint (rs : list reloc) : bool :=
  (fix go (l : list reloc) : bool :=
     match l with
     | [] => true
     | r :: rest =>
         forallb (fun s => orb (Nat.leb (r_offset r + 16) (r_offset s))
                               (Nat.leb (r_offset s + 16) (r_offset r))) rest && go rest
     end) rs.

(* ---- relocation table of the live code object ---------------------------- *)

(* The ports/arm/chez/*.relocs listing: one (#<code NAME> . OFFSET) per line,
   written by the ARM lane's dump from the code object's relocation table. *)
Fixpoint relocs_of_lines (ls : list string) : option (list (string * nat)) :=
  match ls with
  | [] => Some []
  | l :: r =>
      if String.eqb l "" then relocs_of_lines r
      else match read_exactly l with
           | Some (Dot [Atom name] (Atom off)) =>
               if all_digits off then
                 option_map (cons (name, digits_nat off)) (relocs_of_lines r)
               else None
           | _ => None
           end
  end.

(* Template targets are (library-code #(libspec NAME N)). *)
Definition target_code_name (t : sexp) : option string :=
  match t with
  | Lst [Atom k; Vec (Atom l :: Atom name :: _)] =>
      if andb (String.eqb k "library-code") (String.eqb l "libspec")
      then Some ("#<code " ++ name ++ ">") else None
  | _ => None
  end.

Fixpoint table_of (rs : list reloc) : option (list (string * nat)) :=
  match rs with
  | [] => Some []
  | r :: rr =>
      match target_code_name (r_target r), table_of rr with
      | Some n, Some t => Some ((n, r_offset r) :: t)
      | _, _ => None
      end
  end.

Definition pair_eqb (a b : string * nat) : bool :=
  String.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Definition same_table (a b : list (string * nat)) : bool :=
  Nat.eqb (length a) (length b) &&
  forallb (fun x => existsb (pair_eqb x) b) a &&
  forallb (fun x => existsb (pair_eqb x) a) b.

(* ---- captured bytes ------------------------------------------------------ *)

Definition hex_val (c : ascii) : option Z :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 48 n) (Nat.leb n 57) then Some (Z.of_nat (n - 48))
  else if andb (Nat.leb 65 n) (Nat.leb n 70) then Some (Z.of_nat (n - 55))
  else if andb (Nat.leb 97 n) (Nat.leb n 102) then Some (Z.of_nat (n - 87))
  else None.

Fixpoint hex_Z_acc (acc : Z) (s : string) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c r => match hex_val c with Some v => hex_Z_acc (acc * 16 + v)%Z r | None => None end
  end.

(* Lines "OOOO WWWWWWWW": a byte offset and the 32-bit word stored there;
   comment lines start with #.  Offsets must be 0, 4, 8, ... in order. *)
Fixpoint words_of_lines (expect : Z) (ls : list string) : option (list Z) :=
  match ls with
  | [] => Some []
  | l :: r =>
      if orb (String.eqb l "") (prefix "#" l) then words_of_lines expect r
      else if Nat.eqb (String.length l) 13 then
        match hex_Z_acc 0 (substring 0 4 l), hex_Z_acc 0 (substring 5 8 l) with
        | Some off, Some w =>
            if Z.eqb off expect then option_map (cons w) (words_of_lines (expect + 4)%Z r)
            else None
        | _, _ => None
        end
      else None
  end.

Definition bytes_of_hex (text : string) : option (list Z) :=
  option_map (flat_map (le_bytes 4)) (words_of_lines 0 (split_lines text)).

(* ---- locating the code record in np-generate-code output ----------------- *)

(* (code FUNC SUBTYPE FREE "NAME" ARITY SIZE (ENTRY ...) INFO PINFO) *)
Fixpoint find_code (fuel : nat) (name : string) (x : sexp) : option (Z * list sexp) :=
  match fuel with
  | O => None
  | S f =>
      let fix first (xs : list sexp) : option (Z * list sexp) :=
        match xs with
        | [] => None
        | y :: ys => match find_code f name y with Some r => Some r | None => first ys end
        end in
      match x with
      | Lst (Atom k :: _ :: _ :: _ :: Str n :: _ :: size :: Lst entries :: _) =>
          if andb (String.eqb k "code") (String.eqb n name) then
            match z_of_atom size with Some s => Some (s, entries) | None => None end
          else first (Atom k :: entries)
      | Lst xs | Vec xs | Rec xs => first xs
      | Dot xs t => first (t :: xs)
      | Def _ y => find_code f name y
      | _ => None
      end
  end.

(* ---- the checker ---------------------------------------------------------- *)

Definition check_code_object (tmpl : list Z) (rs : list reloc) (size : Z)
    (captured : list Z) (table : list (string * nat)) : bool :=
  Z.eqb (Z.of_nat (length tmpl)) size &&
  Nat.eqb (length captured) (length tmpl) &&
  windows_disjoint rs &&
  forallb (fun r => Nat.leb (r_offset r + 16) (length tmpl)) rs &&
  template_windows_zero tmpl rs &&
  zlist_eqb (instantiate tmpl rs (items_of captured rs)) captured &&
  match table_of rs with Some t => same_table t table | None => false end.

Theorem check_code_object_sound :
  forall tmpl rs size captured table,
    check_code_object tmpl rs size captured table = true ->
    captured = instantiate tmpl rs (items_of captured rs) /\
    template_windows_zero tmpl rs = true /\
    Z.of_nat (length tmpl) = size /\
    (exists t, table_of rs = Some t /\ same_table t table = true).
Proof.
  intros tmpl rs size captured table H.
  unfold check_code_object in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[[[[[Hs Hl] Hd] Hb] Hz] Hi] Ht].
  split.
  - unfold zlist_eqb in Hi.
    destruct (list_eq_dec Z.eq_dec (instantiate tmpl rs (items_of captured rs)) captured)
      as [E|E]; [symmetry; exact E | discriminate].
  - split; [exact Hz|]. split; [apply Z.eqb_eq; exact Hs|].
    destruct (table_of rs) as [t|]; [exists t; split; [reflexivity | exact Ht] | discriminate].
Qed.

