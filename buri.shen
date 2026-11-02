(load "shen/base.shen")
(load "spec/arithmetic.shen")
(load "shen/equations.shen")
(load "shen/kernel.shen")
(load "shen/klambda.shen")
\\ Later captures (compiler schemas, wire, encoder, constructor, EQ-1, ...)
\\ record gensym-numbered local names. Pin the counter to its value after the
\\ pre-Wave-C reference evaluator so that editing shen/klambda.shen does not
\\ renumber unrelated captured code. Reused numbers name only local
\\ parameters and temporaries of compiled definitions.
(set shen.*gensym* 5834)
(load "shen/trace.shen")
(load "shen/claims.shen")
