# DEC: Decoder authentication

> Authenticates cycle decoder data against program-dependent setup tables. Instruction
> execution and generic lookup proof algebra are outside this module.

## Guarantee

An active cycle uses the normalized decoder row assigned to its cycle-start `pc` by
the selected machine profile and circuit family. An unsupported program position
cannot be active. Inactive rows issue no decoder query.

`*` marks a provisional relation whose end-to-end program/setup identity remains
unresolved by `GAP-DEC-001`. The marker is not part of the stable ID.

## Symbols and inputs

| Name | Meaning |
|---|---|
| `P = (P[0], ..., P[L-1])` | raw program text, where each `P[i]` is a 32-bit instruction word |
| `profile` | preprocessing configuration and either the unrolled or unified-reduced circuit layout |
| `family` | selected unrolled circuit family, or the unified-reduced family |
| `N` | decoder-table capacity in words, with `L <= N` and `N` a power of two |
| `pc = pc_lo + 2^16 pc_hi` | 32-bit cycle-start program counter |
| `execute` | cycle-activation value |
| `rs1_index`, `rd_index` | normalized 8-bit decoder fields |
| `rs2_index` | normalized 16-bit field; some delegated operations use it as an ABI value |
| `imm = imm_lo + 2^16 imm_hi` | normalized 32-bit immediate |
| `funct3` | optional 8-bit family-specific auxiliary field |
| `selector_bits[j]` | boolean family-operation selector bits |

`Normalize(profile, P, i)` is the context-aware bytecode preprocessing result at
word position `i`. It may rewrite instruction aliases, immediates, `rd = x0` cases,
and delegated-instruction sequences. `Decode(family, instruction)` either returns
the normalized fields above or returns `unsupported`.

For a family whose circuit retains `funct3` or selector data, define

`selector = sum_j 2^j selector_bits[j]`

and let `Project_family` retain exactly

`(pc_lo, pc_hi, rs1_index, rs2_index, rd_index, imm_lo, imm_hi[, funct3][, selector])`.

The bracketed columns are present only when that family circuit consumes them.
`D[profile, family, P, i]` denotes the resulting projected row, or `unsupported`.
The expression `D[profile, family, P, pc / 4]` also denotes `unsupported` when
`pc mod 4 != 0`.

## Assumptions

- **ASM-DEC-001 — Cycle-start PC domain.** `pc_lo, pc_hi` are each in
  `[0, 2^16)`.
- **ASM-DEC-002* — Program/setup identity.** The accepted decoder setup table is
  the table constructed for the same `(profile, family, P, N)` used by the machine
  proof.
- **ASM-DEC-003 — Lookup admission.** An activated decoder query is admitted only
  when its projected row occurs in the fixed decoder setup table. Generic lookup
  completion and soundness are imported from `LOOKUP`.

## Table relation

### REQ-DEC-001* — Program-derived decoder table

For every `i in [0, N)`:

- if `i < L`, preprocessing succeeds, and
  `Decode(family, Normalize(profile, P, i))` returns decoder data, then
  `D[profile, family, P, i]` is `Project_family` of that data with `pc = 4i`;
- otherwise the materialized table position contains the field value `-1` in every
  retained column. This sentinel is not a row for any admitted 32-bit `pc`.

Raw programs for which preprocessing aborts are rejected during setup construction
and are outside the admitted proof-input boundary. A profile-disabled or
family-unsupported normalized instruction produces the sentinel case instead.

## Cycle relation tree

> Interpret the tree under `ASM-DEC-001..003`. The leaves name the canonical
> requirements; decoder fields on inactive rows may be constrained by other modules.

- **`execute not in {0, 1}`.** Violates `REQ-DEC-002`.
- **`execute = 0`.** `REQ-DEC-002`; no decoder query is activated.
- **`execute = 1`.** `REQ-DEC-002` and `REQ-DEC-003`.
  - **`D[profile, family, P, pc / 4] = unsupported`.** Violates `REQ-DEC-003`.
  - **decoder row exists.** `REQ-DEC-003` binds every retained decoder field to
    that row.

### REQ-DEC-002 — Execute-gated query

`execute in {0, 1}`, and the decoder lookup is activated exactly when
`execute = 1`.

### REQ-DEC-003* — Active row authentication

For `execute = 1`:

`D[profile, family, P, pc / 4] != unsupported`,

and the active projected decoder tuple equals that row. Equivalently, it is the
unique setup-table row whose first two columns encode the admitted `pc`.

## Derived facts

- **Active PC alignment**
  `execute = 1 => pc mod 4 = 0`
- **Atomic decoder row**
  `execute = 1 => active tuple = D[profile, family, P, pc / 4]`
- **Unsupported position**
  `D[profile, family, P, pc / 4] = unsupported => execute = 0`
- **Unique unrolled family**
  `count({family | D[profile, family, P, pc / 4] != unsupported}) <= 1`
- **Inactive decoder**
  `execute = 0 => no decoder query`

## Open boundary

- **GAP-DEC-001 — Accepted setup identity.** Specify and verify the end-to-end edge
  that binds the externally accepted program image to the exact `text_section`,
  profile, family decoder table, and setup commitment used by the proof. Current
  setup APIs accept program-image and text-section inputs separately.

## Metadata

- spec revision: TBD
- implementation: TBD
- profile: unrolled full/unsigned/reduced families and unified reduced machine

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-DEC-001` | normative | active row | `external:CONT` | prose | cycle-start PC state domain | — |
| `ASM-DEC-002` | provisional | setup construction | `GAP-DEC-001`; external proof/setup identity | located | `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type@dfb1b2a8a`; `repo:circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs#unified_reduced_machine_circuit_setup@dfb1b2a8a` | `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type`; `symbol:circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs#unified_reduced_machine_circuit_setup` |
| `ASM-DEC-003` | normative | activated decoder query | `external:LOOKUP` | prose | `spec:lookups/common.md` | — |
| `REQ-DEC-001` | provisional | setup construction | `ASM-DEC-002`; `GAP-DEC-001` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/decoder_trait.rs#process_binary_into_separate_tables_ext@dfb1b2a8a`; family decoder implementations; `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#process_binary_into_separate_tables_ext`; `pattern:cs/src/gkr_circuits/*/decoder.rs#OpcodeFamilyDecoder::define_decoder_subspace (7)`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask` |
| `REQ-DEC-002` | normative | every cycle row | `ASM-DEC-003` | located | `repo:cs/src/cs/circuit_impl.rs#BasicAssembly::allocate_machine_state@dfb1b2a8a`; `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/cs/circuit_impl.rs#BasicAssembly::allocate_machine_state`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REQ-DEC-003` | provisional | `execute = 1` | `ASM-DEC-001..003`, `REQ-DEC-001..002`; `GAP-DEC-001` | located | `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; `repo:prover/src/gkr/prover/setup.rs#GKRSetup::construct@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:prover/src/gkr/prover/setup.rs#GKRSetup::construct` |
| `GAP-DEC-001` | open | — | affects `ASM-DEC-002`, `REQ-DEC-001`, `REQ-DEC-003`; owner `human` | — | setup constructors receive program-image and text-section inputs through distinct parameters; proof-topology binding not yet specified | — |
