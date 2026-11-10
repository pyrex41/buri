From Coq Require Import List ZArith NArith PArith Bool String.
From Buri Require Import JitBytecode JitLowerStage0 JitImage ImgData.
Import ListNotations JitLowerStage0.JitLowerStage0 JitImage.JitImage.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

Definition m0 : mem := mem_of 0 words B.Leaf.
Definition parsed := parse_image m0 nwords.

(* header *)
Definition hdr := option_map (fun '(h, _) => (h_heap h, h_cells h, h_consts h, h_nsym h, h_pcount h)) parsed.

(* object counts by type (0 = pair) *)
Fixpoint bump (t : N) (l : list (N * nat)) : list (N * nat) := match l with
 | [] => [(t, 1%nat)] | (u, k) :: r => if N.eqb t u then (u, S k) :: r else (u, k) :: bump t r end.
Definition type_counts := option_map (fun '(_, c) => fold_left (fun acc '(_, t) => bump t acc) (c_objs c) []) parsed.

(* the definitions' names, in order *)
Definition defname (x : sx) : option positive := match to_val x with
 | B.VPair _ (B.VPair (B.VSym g) _) => Some g | _ => None end.

(* code objects reachable from a code pointer, nested codes included *)
Fixpoint reach (c : ctx) (fuel : nat) (v : N) (acc : list N) : list N :=
 match fuel with O => acc | S f =>
 match deref (c_mem c) (c_hb c) (c_starts c) v 1 8 with
 | None => acc
 | Some a =>
   let cb := get (c_mem c) (a + 4) in let nk := get (c_mem c) (a + 5) in let nc := get (c_mem c) (a + 6) in
   fold_left (fun acc i => reach c f (get (c_mem c) (c_kb c + cb + nk + i)) acc) (seqN 0 (N.to_nat nc)) (a :: acc)
 end end.
Definition fn_ptr (c : ctx) (s : positive) : option N :=
 match B.tget s (c_symcell c) with
 | Some k => match rd (c_mem c) (c_cb c + 2 * k + 1) with
   | Some fv => match deref (c_mem c) (c_hb c) (c_starts c) fv 5 6 with Some a => Some (get (c_mem c) (a + 2)) | None => None end
   | None => None end
 | None => None end.

Definition all_forms := flat_map snd sbc_files.
Definition reached (c : ctx) : B.tree unit :=
 fold_left (fun t x => match defname x with
   | Some g => match fn_ptr c g with Some p => fold_left (fun t a => B.tset (key a) tt t) (reach c 64 p []) t | None => t end
   | None => t end) all_forms B.Leaf.
(* every code object in the heap: (reached?, its name) *)
Definition code_objs := option_map (fun '(_, c) =>
  let r := reached c in
  let codes := filter (fun '(_, t) => N.eqb t 8) (c_objs c) in
  let unr := filter (fun '(o, _) => match B.tget (key (c_hb c + o)) r with Some _ => false | None => true end) codes in
  (List.length codes, List.length unr,
   map (fun '(o, _) => dval c 64 (get (c_mem c) (c_hb c + o + 7))) unr)) parsed.

(* raw SYM_CELL word of each name: sealed bit 58 *)
Definition raw_of (c : ctx) (g : positive) : option N :=
 match find (fun '(s, _, _) => Pos.eqb s g) (symbols (c_mem c) (c_hb c) (c_starts c) (c_objs c)) with
 | Some (_, _, w) => Some w | None => None end.
Definition sealed_by_file := option_map (fun '(_, c) =>
  map (fun '(fl, xs) =>
    let gs := flat_map (fun x => match defname x with Some g => [g] | None => [] end) xs in
    (fl, List.length gs,
     List.length (filter (fun g => match raw_of c g with Some w => N.testbit w 58 | None => false end) gs)))
   sbc_files) parsed.

Definition tally_by_file := option_map (fun '(_, c) =>
  map (fun '(fl, xs) => (fl, tally c (map to_val xs))) sbc_files) parsed.
