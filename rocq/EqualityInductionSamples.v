(* Ground derivations about the captured EQ-1 kernel (Native evaluator, vm
   checked) and its call-graph closure. These are ground facts and sampled
   agreement with the reference kernel, not universal refinement. *)
From Coq Require Import List String ZArith Bool.
From Buri Require Import Native EqualityInductionModel EqualityInductionSpecs EqualityInductionKernel.
Import ListNotations Native.Native.
Module EqualityInductionSamples.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionKernel.EqualityInductionKernel.
Open Scope string_scope.

Fixpoint references e : list string := match e with
 | Lit _ | Var _ => [] | If c a b => references c ++ references a ++ references b
 | Let _ a b | And a b | Or a b => references a ++ references b
 | Call name args => name :: flat_map references args end.
Fixpoint reach fuel (seen todo : list string) := match fuel with
 | O => seen | S n => match todo with
   | [] => seen
   | x :: rest => if existsb (String.eqb x) seen then reach n seen rest else
     let next := match lookup program x with Some d => references (body d) | None => [] end in
     reach n (x :: seen) (rest ++ next) end end.
Definition kernel_reach := Eval vm_compute in reach 2000 [] ["kl:buri.check-bundle"].
(* Proof search, normalisation and evaluation are unreachable from acceptance. *)
Definition search := ["kl:buri.normalize";"kl:buri.norm";"kl:buri.match";"kl:buri.reduce";"kl:buri.bind";
 "kl:buri.matches";"kl:buri.reduce-match";"kl:eval";"eval";"kl:eval-kl";"kl:load";"kl:read-file"].
Theorem acceptance_excludes_search : forallb (fun n => negb (existsb (String.eqb n) search)) kernel_reach = true.
Proof. vm_compute; reflexivity. Qed.
Theorem acceptance_reaches_drivers : forallb (fun n => existsb (String.eqb n) kernel_reach)
 ["kl:buri.bundle-h";"kl:buri.check-theorem";"kl:buri.check-cases";"kl:buri.check-case-bound";"kl:buri.check-steps";
  "kl:buri.instantiate";"kl:buri.replace";"kl:buri.sort";"kl:buri.substitution?";"kl:buri.rules";"kl:buri.theory"] = true.
Proof. vm_compute; reflexivity. Qed.
(* Every reachable callee is a captured definition, a runtime contract, or a
   Native primitive; trap-error appears only as the guard of check-bundle. *)
Definition primitives := ["cons";"list";"car";"cdr";"pair?";"null?";"eq?";"eqv?";"equal?";"number?";
 "integer?";"exact?";"boolean?";"symbol?";"symbol->string";"number->string";"-";">=";"string";"string-ref";
 "substring";"string-length";"error";"kl:shen.f-error";"guard";"Z5963";"else"].
Theorem acceptance_closed : forallb (fun n => existsb (String.eqb n) names || existsb (String.eqb n) primitives)
 kernel_reach = true.
Proof. vm_compute; reflexivity. Qed.

(* Sampled bundles, evaluated by the actual Native evaluator on the captured
   bundle-h and compared with the reference kernel. *)
Definition th name C l r proof := L [sym "theorem";sym name;C;l;r;proof].
Definition step path dir ref sub := L [sym "rewrite";path;sym dir;ref;sub].
Definition nadd_zero_bundle := L [th "t1" (L [L [sym "y";sym "nat"]]) (ap "nadd" [ap "zero" [];v "y"]) (v "y")
 (L [sym "direct";L [step Nil "forward" (L [sym "definition";sym "nadd-zero"]) (L [L [sym "y";v "y"]])]])].
Definition injected_rule_bundle := L [th "bad" (L [L [sym "x";sym "nat"]]) (v "x") (ap "succ" [v "x"])
 (L [sym "direct";L [step Nil "forward" (L [sym "definition";sym "trust-me"]) Nil]])].
Definition forged_label_bundle := L [accepted (L [L [sym "bad";Nil;ap "zero" [];ap "succ" [ap "zero" []]]])].
Definition ill_sorted_bundle := L [th "bad" Nil (ap "zero" []) (ap "halt" []) (L [sym "direct";Nil])].
Definition captured b := run 20000 program "kl:buri.bundle-h" [b;Nil;Integer 10].
Example sample_accepted : captured nadd_zero_bundle =
 Returned (accepted (L [L [sym "t1";L [L [sym "y";sym "nat"]];ap "nadd" [ap "zero" [];v "y"];v "y"]])).
Proof. vm_compute; reflexivity. Qed.
Example sample_injected_rule : captured injected_rule_bundle = Returned (rejected "invalid-rule-instance").
Proof. vm_compute; reflexivity. Qed.
Example sample_forged_label : captured forged_label_bundle = Returned (rejected "malformed-bundle").
Proof. vm_compute; reflexivity. Qed.
Example sample_ill_sorted : captured ill_sorted_bundle = Returned (rejected "ill-sorted-theorem").
Proof. vm_compute; reflexivity. Qed.
Example samples_agree : forallb (fun b => match captured b with Returned v => same v (r_bundle b Nil 10) | _ => false end)
 [nadd_zero_bundle;injected_rule_bundle;forged_label_bundle;ill_sorted_bundle] = true.
Proof. vm_compute; reflexivity. Qed.
End EqualityInductionSamples.
