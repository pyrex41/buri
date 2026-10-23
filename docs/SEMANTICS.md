# Semantic profiles

## BURI/ARITH-1

Sorted first-order terms use `[v name]` for variables and `[symbol args...]` for
applications. The sorts are `nat`, `expr`, `stack`, `code`, and `outcome`.

- Naturals: `zero`, `succ`.
- Expressions: `lit`, `add`, `mul`.
- Stacks: `nil`, `cons` (top first).
- Code: `halt`, `push`, `plus`, `times`, with continuation code in each instruction.
- Outcomes: `ok stack`, `fault`.

All values are finite free-constructor trees. No floats, host pointers, effects,
open globals, or general recursion occur in this profile. Source addition and
multiplication evaluate their operands recursively. Compiled code evaluates
left then right; the VM pops right then left, preserving operand order. Stack
underflow is explicit. Unrelated stack entries remain intact.

The compiler theorem quantifies over arbitrary continuation code and arbitrary
initial stacks, including continuations that fault. The Halt corollary therefore
establishes both the exact result and preservation of the old stack.

The 18 equations in `spec/arithmetic.shen` are the executable definition data.
`buri.normalize` reduces closed sorted terms. Its budget is a conservative depth
bound, not a statement that exhausted terms diverge. Rocq's arithmetic functions
are structurally recursive and total; their correspondence to actual host
execution is not yet proved.

## BURI/EQ-1

A theorem contains a name, universally quantified sorted variables, an equality,
and a proof. A proof is a direct rewrite chain or structural induction on an
`expr` variable. Induction must supply exactly the `lit`, `add`, and `mul` cases.
Constructor argument names are fresh. Only immediate recursive constructor
arguments receive induction hypotheses. Other quantified variables remain
universally instantiable in those hypotheses.

Each rewrite names a definition, an in-scope induction hypothesis, or an already
checked lemma. It supplies a full sorted substitution, direction, and a path of
zero-based argument indices. The selected subterm must equal the instantiated
premise exactly. There is no arbitrary axiom, caller-supplied assumption,
unification oracle, `eval` escape, circular lemma, or implicit normalization rule.

The whole bundle is bound to the complete theory data. A result from an altered
trusted image has no standing in an earlier image.

## BURI/KL-PURE-1 (executable Shen profile)

This is a normalized AST for selected KLambda behavior, not a parser for all
Shen or all KLambda. A frontend correspondence proof is still required.

```text
literal(value) | var(name) | global(name)
lambda(name, body) | apply(function, argument)
let(name, value, body) | if(condition, then, else)
primitive(operator, arguments) | raise(message)
trap(expression, handler) | freeze(body) | thaw(expression)
```

Values distinguish integers, Booleans, strings, symbols, nil, pairs, closures,
partially applied named functions, and thunks. Input literals cannot forge
closures or thunks. Lexical closures capture their definition environment.
Named functions resolve through the closed definition table passed to evaluation;
partial application accumulates arguments until saturation. Global definitions
must have at least one parameter in this release.

Evaluation is left-to-right. Only the chosen branch executes. An exception in a
function expression prevents its argument from running; an exception in an
argument precedes the eventual non-callable error. Trap handlers execute only
on modeled raised outcomes. Frozen expressions retain their lexical environment.

Outcomes are `returned`, `raised`, `unknown`, `unsupported`, or `rejected`.
Unknown budget/host failures are never caught as language exceptions. Unsupported
closure equality is not arbitrarily assigned false. Ground replay reruns the
reference interpreter and checks one claimed outcome; it is not an independent
universal proof.

Mutable globals/vectors, I/O, real-time behavior, dynamic eval/redefinition,
zero-arity global calls, floating arithmetic, and FFI are outside the profile.

## Rocq lexical profile

`rocq/Lambda.v` models literals (Z integers and Booleans), de Bruijn variables,
closures, application, let, conditionals, and addition. It has explicit unbound,
non-callable, non-Boolean, and non-integer errors. Fuel exhaustion is `None`,
distinct from every language outcome. Monotonicity proves that additional fuel
cannot change an obtained result; this yields determinism across fuel bounds.
The let-lowering theorem proves equivalence of terminating outcomes in all
contexts/environments, not termination of arbitrary lambda terms.

This profile currently has no named recursive definitions, exceptions, thunks,
or pairs. It must not be confused with the broader executable Shen profile.

## Native compiler-output validation

`ports/compiler-schemas.shen` supplies 12 fixed KLambda source ASTs with explicit
free-variable scopes. The port's actual `_scm.compile-expression` produces the
Scheme ASTs. The exporter rejects unknown syntax; it supports literals,
variables, integer +/−/*, one-binding let, and sequential let*. Scope resolution
converts both ASTs independently to de Bruijn-indexed formal terms.

`rocq/NativeArithmetic.v` assigns total exact-integer semantics to each AST.
`rocq/NativeOutput.v` proves the resulting equalities for every valuation of
free inputs. These are universally quantified instance-validation theorems,
not an induction proof over all possible inputs to the compiler. Target primitive
correctness, native execution, and decoder fidelity are named assumptions.
