# Profile: L1 Proth120

> Integration stub for the experimental packed L1 proof.

- spec revision: TBD
- implementation: TBD
- status: stub

## Component selections

| Component | Selection |
|---|---|
| ISA | Delegation-free reduced unified ISA |
| Execution | One unified chunk with `2²²` rows |
| Memory | Initialization and teardown folded into the unified chunk |
| Lookups | Unified Proth120 lookup layout |
| Recursion | Experimental packed L1 proof |
| Soundness | Proth120, 100-bit target, `pack_log₂ = 4`, and 20 grinding bits |

Each selection becomes normative only after its owning component module is migrated
and linked here.
