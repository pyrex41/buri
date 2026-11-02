(* E2E-22 ground derivation: the packaged Chez 10.3.0 s/np-languages.ss text
   contains exactly 28 define-language forms; Rocq reads each one, resolves
   every (extends ...) delta itself, and obtains exactly the grammars from
   which rocq/ChezNpSyntax.v's inductive types were generated.  The generator
   (scripts/package-chez-np.py) is therefore not trusted for the grammars. *)
From Coq Require Import String List.
From Buri Require Import ChezNpReader ChezNpGrammar ChezNpLanguagesInput ChezNpSyntax.
Import ListNotations.

Theorem np_languages_form_count :
  length np_language_spans = 28.
Proof. vm_compute. reflexivity. Qed.

Theorem np_languages_spans_complete :
  spans_complete np_languages_source np_language_spans = true.
Proof. vm_compute. reflexivity. Qed.

Theorem np_languages_resolved :
  grammars_of_source np_languages_source np_language_spans = Some generated_grammars.
Proof. vm_compute. reflexivity. Qed.

Theorem np_language_names :
  map fst generated_grammars =
  ["L1"; "L2"; "L3"; "L4"; "L4.5"; "L4.75"; "L4.875"; "L4.9375"; "L5"; "L6"; "L7";
   "L9"; "L9.5"; "L9.75"; "L10"; "L10.5"; "L11"; "L12"; "L12.5"; "L13"; "L13.5";
   "L14"; "L15a"; "L15b"; "L15c"; "L15d"; "L15e"; "L16"]%string.
Proof. vm_compute. reflexivity. Qed.
