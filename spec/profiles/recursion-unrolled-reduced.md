# Profile: recursion unrolled reduced

> Integration stub for proving a recursive verifier with unrolled circuits.

- spec revision: TBD
- implementation: TBD
- status: stub

## Component selections

| Component | Selection |
|---|---|
| ISA | Reduced unrolled ISA and admitted delegations; exact family subset TBD |
| Execution | Per-family unrolled traces with `2²⁴` rows per chunk |
| Memory | Separate initialization/teardown proof |
| Lookups | Per-family lookup layouts |
| Recursion | Unrolled base-layer or recursion-layer verifier program with a `2²⁸`-cycle bound |
| Soundness | BabyBear parameter set, exact values TBD |

Each selection becomes normative only after its owning component module is migrated
and linked here.
