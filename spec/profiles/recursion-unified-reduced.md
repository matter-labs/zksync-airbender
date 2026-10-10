# Profile: recursion unified reduced

> Integration stub for proving the unified recursive verifier.

- spec revision: TBD
- implementation: TBD
- status: stub

## Component selections

| Component | Selection |
|---|---|
| ISA | Reduced unified ISA and admitted delegations; current inventory in [unified profile](../isa/unified/profile.md) and [precompile profile](../isa/precompiles/profile.md) |
| Execution | Unified traces with `2²³` rows per chunk |
| Memory | Initialization and teardown folded into trailing unified chunks |
| Lookups | Unified pooled lookup layout |
| Recursion | Unified recursion verifier program with a `2²⁷`-cycle bound |
| Soundness | BabyBear parameter set, exact values TBD |

Each selection becomes normative only after its owning component module is migrated
and linked here.
