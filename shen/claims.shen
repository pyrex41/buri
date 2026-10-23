\\ Evidence kinds are deliberately not interchangeable.
(tc -)
(define buri.obligations ->
 [[arith-compiler-preservation generic-equation proof-available]
  [arith-equation-interpretation equation-bridge proof-available]
  [lexical-let-lowering generic-equation proof-available]
  [shen-equational-kernel-soundness implementation-refinement open]
  [kl-pure-evaluator-adequacy implementation-refinement open]
  [shen-to-klambda semantic-preservation open]
  [shen-scheme-backend semantic-preservation open]
  [shen-scheme-primitives representation-invariant open]
  [chez-compilation semantic-preservation assumed]
  [gc-and-memory runtime-safety assumed]
  [binary-artifact-binding deployment-correspondence open]
  [system-s-and-pr117 soundness-preservation open]])
\\ Classification is not validation. Only replaying the checker can accept evidence.
(define buri.evidence-kind [accepted generic-equations _] -> generic-equation
  [accepted ground-replay _] -> ground-replay
  [passed conformance _] -> sampled-agreement
  _ -> unknown)
