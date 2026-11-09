# Experimental library scalar replacement

This branch extends the existing late Lsrc scalar-replacement pass, on top of
`cpcse-licm-sra-cost` and the LICM work. Enable the new cases with:

```
CHEZ_SCALAR_REPLACEMENT=1 CHEZ_SRA_LIBRARY=1 CHEZ_SRA_COST=bounded
```

The extension handles the pointer slots allocated by `$record` with a stable
run-time descriptor, a locally bound aggregate returned after effects, and an
aggregate-or-`#f` result. Optional results use a presence flag plus the fields.
The existing constructor/field-count and whole-object escape restrictions still
apply. Descriptor-dependent predicates are folded only when descriptor identity
is proven; arbitrary descriptors with equal layouts are not interchangeable.
Initializer effects and exceptions remain, including unused fields. Nested
closures that return the object remain escapes. Referenced mutable vectors are
not copied or made immutable.

Shape discovery short-circuits an `if` when its first branch has neither an
aggregate shape nor literal `#f`. `CHEZ_SRA_SHAPE_VERIFY=1` compares those decisions
with the previous full-branch query; use this only for validation, not timing.
Optional pairs are rejected before record-only offset/descriptor queries.
`CHEZ_SRA_DEMAND=1` experimentally delays the new shape cases until the existing
walk encounters `$record`; it adds no preliminary traversal and is not the
default. Measurements have not established a compiler-time benefit.
The existing bounded eligibility check and split/helper budgets remain in place.

Run the new semantic checks against a compiler built from this branch:

```
CHEZ_SCALAR_REPLACEMENT=1 CHEZ_SRA_LIBRARY=1 CHEZ_SRA_COST=bounded \
  scheme --script mats/cpsra-library.ss
```

The test compiles cases at optimization levels 0, 2 and 3 with the compiler's
prelex-flag checker enabled. It checks field snapshots across mutation, optional
results in both orientations, descriptor mismatch, mutation/identity escapes,
initializer exceptions, and an escaped closure inside a producer.

This is still a prototype. The Sek experiment additionally uses explicit
`define-inline` producer/accessor definitions to expose operations across Racket
module boundaries. The Chez change does not by itself optimize an opaque
imported producer call. Broad inlining and mutable-container scalarization are
not enabled. A future implementation should export bounded result-shape
summaries and alternate scalar-return entries instead of requiring source
inlining at every consumer.
