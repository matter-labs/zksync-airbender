# UNIFIED: Reduced unified ISA profile

> Inventory of the reduced unified executor at `dfb1b2a8a`; instruction semantics,
> delegation relations, and equivalence with unrolled circuits are specified elsewhere.

`*` marks a profile-specific relation still supported primarily by implementation
evidence and covered by an explicit gap below.

## Guarantee

The profile identifies which preprocessed instructions enter the reduced unified
circuit, which instruction families are absent, and which delegation circuits can
fulfil its delegation calls. It also fixes the structural boundary of "unified": one
executor circuit and setup replace the per-family executor circuits and setups.

## Supported operations

### REQ-UNIFIED-001* — Unified decoder domain

After preprocessing, the unified decoder admits exactly the following source
operations and machine-interface operations:

| Class | Operations |
|---|---|
| Ordinary integer | `NOP`; `ADD`, `ADDI`, `LUI`; `SUB`; `AUIPC` |
| Jump, branch, compare | `JAL`, `JALR`; `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`; `SLT`, `SLTI`, `SLTU`, `SLTIU` |
| Bitwise and shift | `AND`, `ANDI`, `OR`, `ORI`, `XOR`, `XORI`; `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`, `SRAI` |
| Word memory | `LW`, `SW` |
| Modular/custom arithmetic | `ZimopAdd`, `ZimopSub`, `ZimopMul`, `ZimopFMA`, `ZimopTriAdd` |
| Unified xor-rotate | `ZimopIXorRot` with rotation `r in {16, 12, 8, 7}` |
| Machine interface | `ZicsrDelegation`, `ZicsrNonDeterminismRead`, `ZicsrNonDeterminismWrite` |

Source-level register and immediate forms that preprocessing maps to the same decoder
row share one unified operation class. In particular, `ZimopMul` is a custom modular
operation and is not the standard RISC-V `MUL` instruction.

### REQ-UNIFIED-002 — Reduced-family boundary

The profile has no standard multiply/divide family: `MUL`, `MULH`, `MULHSU`, `MULHU`,
`DIV`, `DIVU`, `REM`, and `REMU` are absent. It also has no subword-memory family:
`LB`, `LBU`, `LH`, `LHU`, `SB`, and `SH` are absent. These are profile exclusions,
not unfinished branches of the unified circuit.

### REQ-UNIFIED-003* — Unified-only custom operations

The two operations added directly by the unified decoder are:

- `ZimopTriAdd`: `rd <- (rd + rs1 + rs2) mod 2^32`;
- `ZimopIXorRot`: `rd <- rotate_right(rs1 XOR rd, r)` for
  `r in {16, 12, 8, 7}`, where the right-hand `rd` is its pre-cycle value.

The corresponding standalone add/sub and binary/shift decoders do not admit these
operations at the inspected revision.

### REQ-UNIFIED-004 — Word-memory alignment

For an active unified `LW` or `SW`, the 32-bit effective byte address satisfies
`addr mod 4 = 0`. The unified word-memory body imposes this restriction for both
mutable RAM and ROM accesses.

## Delegation interface

### REQ-UNIFIED-005* — Delegation variants

`ZicsrDelegation` emits a delegation request from the unified executor. The inspected
setup supplies four separate fulfilment-circuit variants:

- Blake2s compression with extended control;
- Blake2s G function;
- bigint operations with control;
- Keccak-f special-5.

These circuits are not fused into the unified executor. Their delegation type and
global invocation/fulfilment argument connect them to the executor profile.

## Circuit structure

### REQ-UNIFIED-006 — Single executor circuit

The unified profile uses one decoder family, one compiled GKR circuit, and one setup
entry for all operations in `REQ-UNIFIED-001`. Each active row selects one of four
embedded executor bodies:

1. add/sub/LUI/AUIPC/modular operations and machine-interface operations;
2. jumps, branches, and comparisons;
3. bitwise and shift operations;
4. word loads and stores.

The bodies share one machine-state allocation, three register-or-memory access slots,
scratch columns, and pooled lookup slots. The unrolled profile instead gives each
instruction family its own compiled circuit, trace, and setup entry. Delegation
circuits remain separate in both structures.

## Open boundary

- **GAP-UNIFIED-001 — Common-ISA equivalence.** No reviewed theorem or exhaustive
  conformance check currently establishes that every ordinary operation shared by
  the unified and unrolled profiles accepts exactly the same architectural
  transition after preprocessing. Such a result is required before one
  implementation-independent ISA relation can discharge both profiles.
- **GAP-UNIFIED-002 — Profile-specific operation adoption.** Review and adopt the
  exact unified decoder inventory, custom `ZimopTriAdd`/`ZimopIXorRot` relations, and
  delegation variants. These claims are currently supported primarily by the unified
  implementation and setup inventory rather than an independent project reference.

## Metadata

The reduced-family boundary, word-alignment rule, and single-circuit structure are
normative for this selected profile: they reflect explicit project direction and
convergent decoder, circuit, setup, and shared-memory evidence. Starred claims remain
provisional because their exact custom inventory or interface is supported primarily
by the current implementation and is tracked by `GAP-UNIFIED-002`.

- spec revision: `2026-08-28.5`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a`
- profile: reduced unified machine, circuit family `128`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REQ-UNIFIED-001` | provisional | decoded executing row | `GAP-UNIFIED-002`; decoder preprocessing boundary | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace` |
| `REQ-UNIFIED-002` | normative | profile selection | `REQ-UNIFIED-001` | located | unified decoder dispatch at `dfb1b2a8a`; unrolled-only family setup inventory | `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type` |
| `REQ-UNIFIED-003` | provisional | `ZimopTriAdd || ZimopIXorRot` | `REQ-UNIFIED-001`; `GAP-UNIFIED-002` | located | `repo:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace@dfb1b2a8a`; unified family bodies | `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/binary_shifts.rs#apply_unified_binary_shifts_inner` |
| `REQ-UNIFIED-004` | normative | active `LW || SW` | `REQ-UNIFIED-001` | located | `repo:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs#apply_unified_mem_word_only_lw_sw_data_path@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs#apply_unified_mem_word_only_lw_sw_data_path` |
| `REQ-UNIFIED-005` | provisional | delegation request and fulfilment | `REQ-UNIFIED-001`; `GAP-UNIFIED-002`; external global delegation argument | located | `repo:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner@dfb1b2a8a`; `repo:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner`; `symbol:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations` |
| `REQ-UNIFIED-006` | normative | profile construction | `REQ-UNIFIED-001` | located | `repo:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core@dfb1b2a8a`; `repo:circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs#unified_reduced_machine_circuit_setup@dfb1b2a8a`; per-family setup path | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core`; `symbol:circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs#unified_reduced_machine_circuit_setup`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type` |
| `GAP-UNIFIED-001` | open | — | affects common ISA adoption; owner `human` | — | shared operation names and structurally adapted family bodies; no accepted equivalence artifact | — |
| `GAP-UNIFIED-002` | open | — | affects `REQ-UNIFIED-001`, `REQ-UNIFIED-003`, `REQ-UNIFIED-005`; owner `human` | — | exact unified-only inventory and relations currently have implementation evidence but no independent adopted project reference | — |
