(load "tests/support.shen")
\\ E2E-21 sampled checks on the host Shen-Scheme v0.52 (x86_64). Ground
\\ observations of one process, not theorems. They record where the Chez
\\ representation of a Shen value is not what rocq/KLSemantics.v rule_intern
\\ prescribes (VSym t for every name other than "true"/"false").
\\ Counterexample: kl:intern (shen-scheme src/primitives.scm) maps a name of
\\ length > 1 whose first character is a digit through string->number.
(buri.test intern-numeric-is-integer (integer? (intern "12")) true)
(buri.test intern-numeric-is-not-symbol (symbol? (intern "12")) false)
(buri.test intern-numeric-equals-number (= (intern "12") 12) true)
(buri.test intern-negative-stays-symbolic (integer? (intern "-5")) false)
(buri.test intern-single-digit-not-converted (integer? (intern "7")) false)
\\ Booleans are the Chez #t/#f immediates, not symbols (VALUE-MODEL row 1).
(buri.test intern-true-is-boolean (boolean? (intern "true")) true)
(buri.test intern-true-not-symbol (symbol? (intern "true")) false)
(buri.test intern-ordinary-symbol (symbol? (intern "abc")) true)
(buri.done)
