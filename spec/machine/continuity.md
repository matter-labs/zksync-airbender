# CONT: Cycle-state continuity

> This module specifies program-counter and timestamp continuity across active CPU
> cycles. Register state, RAM/ROM state, instruction semantics, and the final-state
> acceptance policy are specified elsewhere.

## Guarantee

Active cycles form one state chain beginning at `(pc, ts) = (0, 4)`. The authenticated
ISA-family relation determines each cycle's next `pc`; this module advances `ts` by
four and connects the cycle end to the next active cycle through the typed global
permutation. Inactive padding rows do not extend the chain.

## Symbols

- `u32 = [0, 2^32)`.
- `T = [0, 2^38)` — the timestamp domain, represented by two 19-bit limbs.
- `execute_i : {0, 1}` — activation flag for physical row `i`.
- `C_i^start = (pc_i^start, ts_i^start)` and
  `C_i^end = (pc_i^end, ts_i^end)` — the state endpoints of an active cycle.
- `PCState(pc, ts)` — the typed global-permutation tuple with address-space tag
  `PC`, empty address, value `pc`, and timestamp `ts`.
- `R_f` — the authenticated ISA-family relation selected for the cycle.

## Assumptions

- **ASM-CONT-001 — Authenticated family dispatch.** On an active row, the decoder
  authenticates exactly one supported operation and selects its ISA-family relation
  `R_f`.
- **ASM-CONT-002 — PC-owner dispatch.** The jump/branch/set-less-than relation
  determines `pc_i^end` for its control-flow and sequential cases. Every other selected
  ISA-family relation determines its sequential `pc_i^end`. The unified implementation's
  common sequential-PC constraint is a factorization of this rule, not a second PC
  assignment.
- **ASM-CONT-003 — Typed-permutation guarantee.** Equality of the accepted global
  permutation products binds equality of the typed read and write tuple multisets.

## Canonical relation tree

> Interpret the tree under `ASM-CONT-001..003`. It is a navigation view; the
> identified statements below are canonical.

- **`execute_i = 0`.** The row is padding and contributes no decoder query or
  architectural state tuple. `REQ-CONT-001`.
- **`execute_i = 1`.** The row is an active cycle. `REQ-CONT-001`.
  - **`R_f` is the jump/branch/set-less-than relation.** That relation supplies
    `pc_i^end`; apply `REQ-CONT-003`, `REQ-CONT-004`, and `REQ-CONT-005`.
  - **`R_f` is any other supported ISA-family relation.** Its sequential-PC clause
    supplies `pc_i^end`; apply `REQ-CONT-003`, `REQ-CONT-004`, and
    `REQ-CONT-005`.

Initialization and whole-trace closure are `REQ-CONT-002` and `REQ-CONT-006`.

## Requirements

### REQ-CONT-001 — Activation boundary

`execute_i` is Boolean. If `execute_i = 0`, the decoder lookup and the PC-state
read/write pair are both masked to their argument identities. Such a row creates no
architectural transition. If `execute_i = 1`, both are active.

### REQ-CONT-002 — Initial cycle state

The first active cycle starts at:

`C_0^start = (0, 4)`.

### REQ-CONT-003 — State domains and alignment

For every active cycle:

```text
pc_i^start, pc_i^end in u32
pc_i^start mod 4 = 0
pc_i^end mod 4 = 0
ts_i^start, ts_i^end in T
```

The PC relation rejects an assignment outside `u32`; it does not wrap through
`2^32`. The timestamp relation likewise rejects an assignment outside `T`.

### REQ-CONT-004 — Timestamp step

For every active cycle, the integer relation is:

```text
ts_i^start + 4 < 2^38
ts_i^end = ts_i^start + 4
```

### REQ-CONT-005 — Local PC-state contribution

Every active cycle contributes exactly this typed pair to the global permutation:

```text
read:  PCState(pc_i^start, ts_i^start)
write: PCState(pc_i^end,   ts_i^end)
```

The selected `R_f` constrains `pc_i^end`; this module does not repeat its instruction
equation.

### REQ-CONT-006 — Whole-trace closure

For the active cycles, the PC-tagged projection of the global permutation closes as
the multiset equality below, where `+` denotes multiset union:

```text
{PCState(0, 4)} + {PCState(pc_i^end, ts_i^end)}_i
  = {PCState(pc_final, ts_final)} + {PCState(pc_i^start, ts_i^start)}_i
```

The left boundary is injected as a write and the claimed final state as a read. Under
`ASM-CONT-003`, this connects every active cycle end to the next active cycle start;
padding rows add neither endpoint.

## Derived facts

- **Timestamp sequence**
  `ts_0^start = 4`
  `ts_j^start in {4, 8, 12, ...}` for active cycle `j`
  `ts_j^start < ts_(j+1)^start`
- **PC alignment**
  `pc_i^start mod 4 = 0`
  `pc_i^end mod 4 = 0`
- **Cycle continuity**
  `C_i^end = C_j^start` for consecutive active cycles `i` and `j`
- **Empty trace**
  `(pc_final, ts_final) = (0, 4)`

## Metadata

The continuity relation is normative for the selected machine profiles. PC behavior
follows the adopted ISA relations; timestamp domains, activation, and global closure
are supported by matching constants, compiler constraints, boundary contributions,
and full-statement-verifier checks at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled machine families and reduced unified machine

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-CONT-001` | normative | active row | `external:DEC`; `external:UPROF`; `external:UNIFIED` | located | `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; `repo:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_family_dispatch_one_hot@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_family_dispatch_one_hot` |
| `ASM-CONT-002` | normative | active row | `ASM-CONT-001`; `external:UPROF`; `external:UNIFIED` | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a`; `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_reduced_machine_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_pc_bump` |
| `ASM-CONT-003` | normative | accepted global argument | `external:BASE` | located | `repo:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation@dfb1b2a8a`; `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a`; `repo:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REQ-CONT-001` | normative | every physical row | — | located | `repo:cs/src/cs/circuit_impl.rs#Circuit::allocate_machine_state@dfb1b2a8a`; `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/cs/circuit_impl.rs#Circuit::allocate_machine_state`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REQ-CONT-002` | normative | trace boundary | — | located | `repo:common_constants/src/lib.rs#INITIAL_PC@dfb1b2a8a`; `repo:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP@dfb1b2a8a`; `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@dfb1b2a8a` | `symbol:common_constants/src/lib.rs#INITIAL_PC`; `symbol:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP`; `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions` |
| `REQ-CONT-003` | normative | active cycle | `ASM-CONT-002`; `REQ-CONT-002`; `REQ-CONT-006` | located | `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a`; `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REQ-CONT-004` | normative | active cycle | `REQ-CONT-003` | located | `repo:common_constants/src/timestamps.rs#TIMESTAMP_STEP@dfb1b2a8a`; `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:common_constants/src/timestamps.rs#TIMESTAMP_STEP`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REQ-CONT-005` | normative | active cycle | `ASM-CONT-002`; `REQ-CONT-001`; `REQ-CONT-004` | located | `repo:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| `REQ-CONT-006` | normative | accepted execution statement | `ASM-CONT-003`; `REQ-CONT-002`; `REQ-CONT-005` | located | `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@dfb1b2a8a`; `repo:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits@dfb1b2a8a`; `repo:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit@dfb1b2a8a` | `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
