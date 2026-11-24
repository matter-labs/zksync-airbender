# Clean definitions used by the specification

CleanCore is the part of Clean that the specification and proofs use, transcribed
into the Airbender namespace. [lakefile.toml](../../lakefile.toml) pins Clean tag
v4.35.0 at commit b41c196b10cf0f389d2badf5e19e1435e78e6d98.
The transcription places every definition that gives a claim its meaning in the
[reviewed specification](../README.md), with its own import boundary.

| File | Definitions and users |
| --- | --- |
| [Circuit/Expression.lean](Circuit/Expression.lean) | Variables, expressions and evaluation for imported circuit equations. |
| [Circuit/Lookup.lean](Circuit/Lookup.lean) | Tables and lookup containment for circuit and native lookup claims. |
| [Circuit/Operations.lean](Circuit/Operations.lean) | Flat assertions, lookups and constraint satisfaction for all circuit families. |
| [Circuit/Provable.lean](Circuit/Provable.lean) | Typed field layouts used by table and lookup rows. |
| [Specs/BLAKE3.lean](Specs/BLAKE3.lean) | BLAKE3 reference constants and mixing functions used by hash circuit models. |
| [Specs/Keccak256.lean](Specs/Keccak256.lean) | Keccak-f[1600] reference used by Keccak circuit and delegation claims. |
| [Utils/Bitwise.lean](Utils/Bitwise.lean) | Bit operations and rotations used by hash and integer circuit models. |
| [Utils/Field.lean](Utils/Field.lean) | Byte and field conversion definitions used by word and circuit models. |
| [Utils/OfflineMemory.lean](Utils/OfflineMemory.lean) | Timestamped memory accesses and consistency used by memory histories. |

[Equivalence.lean](Equivalence.lean) proves that each definition equals its Clean
counterpart. For constraint semantics, the equality uses the translation
`toClean`. This module is a leaf: no module imports it. The required kernel replay
checks it with leanchecker because lake check does not export this leaf.
The [module comment](Equivalence.lean) lists the deviations from Clean.

Read the definitions used by the claims, then the correspondence statements in
[Equivalence.lean](Equivalence.lean). The kernel checks the correspondence proofs.
