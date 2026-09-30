# Profile: base unrolled full unsigned

> Integration stub for the application base-proof profile.

- spec revision: TBD
- implementation: TBD
- status: stub

## Component selections

| Component | Selection |
|---|---|
| ISA | Full unsigned unrolled ISA and admitted precompiles; current inventory in [unrolled profile](../isa/unrolled/profile.md) and [precompile profile](../isa/precompiles/profile.md) |
| Execution | Per-family unrolled traces with `2²⁴` rows per chunk |
| Memory | Separate initialization/teardown proof |
| Lookups | Per-family lookup layouts |
| Recursion | Application base proof |
| Soundness | BabyBear parameter set, exact values TBD |

Each selection becomes normative only after its owning component module is migrated
and linked here.
