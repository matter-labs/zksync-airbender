# Airbender proof-system specification

- spec revision: TBD
- implementation: TBD
- scope: unrolled and reduced-unified ISA implementations and their proof system

## Specification order

1. **[ISA](isa/)**
   Instruction and precompile relations: supported operations, inputs, state
   assignments, and profile-dependent ISA variants

2. **[Execution](execution/)**
   Machine execution: ISA dispatch, cycles, chunks, trace layout, activation,
   padding, and within-chunk continuity

3. **[Memory](memory/) and [lookups](lookups/)**
   Read and read-write arguments: register, ROM, and RAM histories;
   initialization and teardown; decoder and fixed-table membership; range checks;
   and lookup or permutation consistency

4. **[Recursion](recursion/)**
   Proof composition: base proofs, aggregation, cross-proof continuity, recursive
   verifier roles, proof topology, and final acceptance

5. **[Soundness](soundness/)**
   Security parameters and error accounting: fields, hashes, polynomial
   commitments, queries, grinding, and composed soundness bounds

## Profiles

[Profiles](profiles/) are manifests, not another proof-system layer. Each profile
selects one compatible configuration across the five sections above.

## Supporting documents

- [HIERARCHY.md](HIERARCHY.md) records module ownership and the migration layout
- [METADATA.md](METADATA.md) defines statement metadata and source locators
- [ETHPROOFS-W2.md](ETHPROOFS-W2.md) maps the specification to the official W2
  requirements
- `machine-old/` retains legacy material until its relations move to their
  canonical sections above
