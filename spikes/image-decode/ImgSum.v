From Coq Require Import List NArith String Ascii.
From Buri Require Import JitBytecode JitImage ImgRun.
Import ListNotations JitImage.JitImage.
Open Scope string_scope.
Definition N2n := N.to_nat.
Definition txt (t : list N) : string := string_of_list_ascii (map ascii_of_N t).
Definition vname (v : option JitBytecode.JitBytecode.val) : string :=
 match v with Some (JitBytecode.JitBytecode.VSym p) => txt (JitBytecode.JitBytecode.text_of_sym p) | _ => "?" end.
Definition vf (v : verdict) : string := match v with
 | Match f => "match " ++ txt (JitBytecode.JitBytecode.text_of_sym f)
 | Differ f => "differ " ++ txt (JitBytecode.JitBytecode.text_of_sym f)
 | Unbuilt f => "unbuilt " ++ txt (JitBytecode.JitBytecode.text_of_sym f)
 | Undecoded f => "undecoded " ++ txt (JitBytecode.JitBytecode.text_of_sym f)
 | Unparsed => "unparsed" end.
Definition s_hdr := Eval vm_compute in
 option_map (fun '(a, b, c, d, e) => [N2n a; N2n b; N2n c; N2n d; N2n e]) hdr.
Print s_hdr.
Definition s_types := Eval vm_compute in option_map (map (fun '(t, k) => (N2n t, k))) type_counts.
Print s_types.
Definition s_sealed := Eval vm_compute in sealed_by_file.
Print s_sealed.
Definition s_tally := Eval vm_compute in
 option_map (map (fun '(fl, (n, bad)) => (fl, n, map vf bad))) tally_by_file.
Print s_tally.
Definition s_total := Eval vm_compute in
 option_map (fun l => fold_left (fun acc '(_, (n, bad)) => (fst acc + n, snd acc + List.length bad)%nat) l (0%nat, 0%nat))
   tally_by_file.
Print s_total.
Definition s_codes := Eval vm_compute in
 option_map (fun '(a, b, ns) => (a, b, map vname ns)) code_objs.
Print s_codes.
