From Coq Require Import String.
From Buri Require Import CLPortGuard.
Import CLPortGuard.CLPortGuard.
Open Scope string_scope.
Definition captured_guard : sexp := (Pair (Sym "COMMON-LISP:DEFUN") (Pair (Sym "SHEN:shen-cl.true?") (Pair (Pair (Sym "SHEN:X") Nil) (Pair (Pair (Sym "COMMON-LISP:COND") (Pair (Pair (Pair (Sym "COMMON-LISP:EQ") (Pair (Pair (Sym "COMMON-LISP:QUOTE") (Pair (Sym "SHEN:true") Nil)) (Pair (Sym "SHEN:X") Nil))) (Pair (Pair (Sym "COMMON-LISP:QUOTE") (Pair (Sym "COMMON-LISP:T") Nil)) Nil)) (Pair (Pair (Pair (Sym "COMMON-LISP:EQ") (Pair (Pair (Sym "COMMON-LISP:QUOTE") (Pair (Sym "SHEN:false") Nil)) (Pair (Sym "SHEN:X") Nil))) (Pair Nil Nil)) (Pair (Pair (Sym "COMMON-LISP:T") (Pair (Pair (Sym "SHEN:simple-error") (Pair (Pair (Sym "COMMON-LISP:FORMAT") (Pair Nil (Pair (Text "boolean expected: not ~A~%") (Pair (Sym "SHEN:X") Nil)))) Nil)) Nil)) Nil)))) Nil)))).
Theorem captured_guard_admitted : admitted captured_guard = true.
Proof. vm_compute. reflexivity. Qed.
Theorem captured_guard_correct : forall x, run captured_guard x = strict_guard x.
Proof. intros. apply actual_guard_refinement. exact captured_guard_admitted. Qed.
