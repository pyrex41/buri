# Checked observer IO and arbitrary binding lists

## A native counterexample

On the pinned Shen-Scheme image, setting `*hush*` to true and calling
`write-to-file` with nonempty text returns the requested text but leaves the file
empty. The kernel's writer uses `pr`, which observes the hush flag. The observer
previously treated that return as sufficient evidence of writing its snapshots
and captures. Fresh shell gates could detect missing/mismatched files, but the
native observer function itself could return normally after a suppressed write.

`buri.checked-write` now performs the write, reads the path back and compares the
observed text with the requested text. Mismatch raises `Snapshot write
verification failed`. The controlled encoder and constructor observers use it
for every output, including source snapshots, bit captures and transcripts.

The behavior is fail-closed for publication acceptance, not transactional: an
unsuccessful attempt may truncate or partially alter a file. It does not roll
back already installed procedures or records. Thirteen native cases distinguish
the old counterexample, checked rejection, valid empty text, observer failure,
normal output recovery and an invalid path.

## Captured wrapper execution proof

The wrapper is the fourth actual definition captured from
`shen/observe-encoder.shen`. `CheckedIOInput.v` selects that exact body and checks
its name and typed decoding. `CheckedFileIO.v` executes it with the seven pinned
helpers in the existing effect interpreter, now parameterized by an operation
handler. This is not a hand-written replacement for the wrapper algorithm.

The model file world is a finite list of path/text pairs with first-match lookup.
The writer is arbitrary: it may report success without changing the world,
corrupt the requested contents, partially mutate the world, or report an error.
The read operation observes the current requested path in that world. Theorems
establish:

- Exact captured control flow and effect trace for every writer response/world.
- Every successful wrapper return is the requested text, and lookup of the
  requested path in its final world returns exactly that text.
- Observed corrupt contents cause mismatch rejection.
- A failed writer response is preserved, with no subsequent read operation.

The read-back contract remains trusted at the native boundary. If reads lie,
string equality is rebound, the native execution differs from the model, or the
file changes after checking, this theorem does not establish future file
contents. It checks text in the admitted representation, not independently
verified filesystem bytes, atomic rename, fsync/durability or resource cleanup.
Missing modeled files are unsupported rather than accepted; native error payload
correspondence is not claimed for that case.

The proof separates the write, read and equality stages before composing them.
This avoids reducing neutral effectful continuations into an unnecessarily large
proof term. Six evaluator depth units suffice for this exact wrapper; they are
not a native instruction, time or heap bound.

The captured observer entry is also checked for a single binding of its source
variable and three checked-write calls with no direct `write-to-file` token.
These AST facts supplement the execution proof of the wrapper. They do not prove
execution of every higher-order operation in the complete observer entry.

## Compiler preservation for arbitrary binding lists

`CompilerBindings.v` extends the source-pinned upstream `merge-nested-lets` pass
from two bindings to arbitrary lists. Both the original nested `let`/`let*` and
the emitted merged `let*` decode to exactly the same lexical expression. This
covers empty lists, arbitrary length and shadowing by repeated names. Every pure
result, error, unsupported outcome and fuel exhaustion is identical. Effects
also agree for an arbitrary supplied handler, including the checked-IO handler.

The syntax-admission relation states that each subexpression decodes to the same
expression at every sufficient reader depth. Literal, variable, conditional and
let lemmas construct admitted inputs; callers must establish the remaining
premises for their own syntax. This is not a universal correctness theorem for
all native Scheme syntax or the entire Shen compiler. A separate composed theorem
links the actual captured pass's machine execution to the semantic preservation
statement, rather than only comparing a parallel transformation model.

All changed captures are regenerated from fresh loads, including the new generated
names caused by the observer helper. Two new altered-wrapper cases must fail
Rocq proof checking. Packaging mismatch and stale-output checks cover the new
proof input. `coqchk` and the custom-axiom audit remain mandatory.
