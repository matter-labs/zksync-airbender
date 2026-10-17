# Proof profiles

> Each profile binds one selection from the ISA, execution, memory, lookups,
> recursion, and soundness components. Component relations remain canonical in their
> owning directories.

- spec revision: TBD
- implementation: TBD
- status: integration stubs

## Profiles

| Profile | Proof role |
|---|---|
| [base-unrolled-full-unsigned.md](base-unrolled-full-unsigned.md) | application base proof |
| [recursion-unrolled-reduced.md](recursion-unrolled-reduced.md) | unrolled recursive verifier proof |
| [bridge-unified-reduced.md](bridge-unified-reduced.md) | unrolled-to-unified bridge proof |
| [recursion-unified-reduced.md](recursion-unified-reduced.md) | unified recursive verifier proof |
| [l1-proth120.md](l1-proth120.md) | experimental packed L1 proof |

Every manifest selects:

- ISA and precompiles
- execution layout and chunk bounds
- memory initialization and teardown packaging
- lookup layout
- recursion role
- soundness parameters

The manifests are incomplete until every selection links to an adopted component
relation.
