# Source snapshots and live dependency checks

Three additions strengthen the controlled execution lane:

1. The observer reads the file once into a string, passes that same string to
   `read-from-string`, and saves it beside the capture as `.bits.source`. The
   proof gate compares those bytes with the source-bound encoder. This removes
   a second file read between snapshot and parsing; reader correctness and
   truthful observer execution remain assumed.
2. `shen/binding-guard.shen` enumerates encoder bindings, decimal-classification
   helpers, and named Scheme runtime dependencies. The report binds the inventory,
   helper source, source snapshot and host hashes. The inventory includes some
   transitive Shen helpers but does not claim the full runtime dependency closure:
   floor/symbol classification internals, Chez internals, globals and mutable
   objects beneath procedures remain outside this inventory.
3. `buri.seal-encoder` snapshots the actual procedure values, and
   `buri.guarded-wire` refuses to run if any inventoried binding changes. The
   exact ordered inventory is required; omitted and extra entries fail. Metadata
   changes alone do not invalidate procedure identity. A second check follows
   execution, before the result is returned.

The guard is trusted live execution tooling. It is not an inert proof checker,
cryptographic certificate, or automatic authorization to trust a new snapshot.
Callers must obtain the snapshot after a validated installation in a controlled
process. The guard and its dependencies themselves must remain trusted. Source
hashes do not prove source-to-binary correspondence.

`BindingVersions.v` proves exact equality, coverage of every index, and rejection
of a changed version in an abstract version-vector model. This is not yet a
refinement proof of the Shen/native identity implementation. Native tests cover
real helper rebinding, omission, extra entries, metadata independence and refusal
before execution. They remain tests, separate from the formal model.

The pre/post checks are for sequential controlled execution. They do not stop
concurrent changes, transient changes restored before checking, or mutation of
objects reachable through an unchanged procedure. No immutable runtime namespace
or atomic execution transaction has been implemented. Complete tagging-adapter
verification and primitive/runtime refinement are still open.
