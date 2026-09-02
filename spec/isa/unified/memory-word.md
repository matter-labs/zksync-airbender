# UMWORD: Unified word memory family

## Supported operations

- `LW rd, imm12(rs1)` with `rd ≠ x0`
- `SW rs2, imm12(rs1)`

The reduced unified profile has no subword-memory operations. Preprocessing replaces
`LW x0, imm12(rs1)` by `NOP`, which is outside this module. The emulated machine has
no MMIO, device-side-effect, or architectural exception channel.

## Inputs

- `u12 = [0, 2¹²)` and `u32 = [0, 2³²)` are unsigned integer domains
- `pc, rs1, rs2 ∈ u32`
- `execute ∈ {0, 1}` activates the cycle
- `imm12 ∈ u12` is the encoded load or store immediate
- `rd ≠ x0` is the `LW` destination register
- `op ∈ {LW, SW}`
- `sign_extend_12(x)` sign-extends `x ∈ u12` to `u32`
- `ROM[a] ∈ u32` is the authenticated program-image word at byte address `a`
- `RAM[a] ∈ u32` is the mutable word at byte address `a`
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-UMWORD-001 — Decoder authentication.** For an active row, the unified decoder authenticates exactly one of `LW` or `SW`, its selected registers, and `sign_extend_12(imm12)` against the instruction at the current `pc`
- **ASM-UMWORD-002 — Register and memory consistency.** Register and RAM accesses satisfy the shared global arguments
- **ASM-UMWORD-003 — ROM authenticity.** For `a < 2²²`, `ROM[a]` is the authenticated program-image word at `a`, or zero padding after the supplied image; the ROM table admits exactly the multiples of four
- **ASM-UMWORD-004 — Zero register.** Reading `x0` returns `0`
- **ASM-UMWORD-005 — PC domain and alignment.** The cycle-start `pc` belongs to `u32` and the active decoder row implies `pc mod 4 = 0`

## Canonical relation tree

> Interpret this tree under `ASM-UMWORD-001..005`. Within `execute = 1`, the numbered
> relations are conjoined. The cases below `REL-UMWORD-002` are mutually exclusive.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-UMWORD-001`] Effective address**
    `addr = (rs1 + sign_extend_12(imm12)) mod 2³²`
  - **[`REL-UMWORD-002`] Word-memory assignment**
    `addr mod 4 = 0`
    - **`op = LW`**
      - **`addr < 2²²`**
        `rd ← ROM[addr]`
      - **`addr ≥ 2²²`**
        `rd ← RAM[addr]`
    - **`op = SW`**
      `addr ≥ 2²²`
      `RAM[addr] ← rs2`
  - **[`REL-UMWORD-003`] Non-wrapping PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

- **32-bit effective address**
  `addr ∈ u32`
- **ROM immutability**
  `ROM` unchanged
- **Register and memory effects**
  `op = LW ⇒ only rd may change`
  `op = SW ⇒ only RAM[addr] may change`
- **PC range**
  `pc ≤ 2³² − 8` before assignment
  `pc ≤ 2³² − 4` after assignment
- **PC alignment**
  `pc mod 4 = 0`

## Metadata

These relations are normative for the reduced unified profile. Effective-address,
load, and store semantics adopt the official
[RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).
The [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate `LW`, `SW`, and `pc ← pc + 4`. Airbender additionally fixes the ROM
boundary, suppresses `LW x0` during preprocessing, requires aligned unified memory
accesses, and forbids PC overflow. The relation is derived directly from the unified
implementation and these adopted sources; it does not assume equivalence with the
unrolled family.

- spec revision: `2026-09-02.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a`
- profile: reduced unified machine, Family 4 `LW`/`SW` subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-UMWORD-001` | normative | active row | `external:DEC`; `REQ-UNIFIED-001` | located | unified preprocessing and decoder at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace` |
| `ASM-UMWORD-002` | normative | active row | `external:REG`; `external:MEM` | located | shared register/RAM dispatch and unified global memory argument at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only.rs#apply_unified_mem_word_only_inner`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_reduced_machine_inner`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `ASM-UMWORD-003` | normative | ROM load | `external:MEM/ROM` | located | aligned program-image table and `ROM_BYTE_SIZE_LOG2 = 22` at `dfb1b2a8a` | `symbol:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2`; `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image`; `symbol:circuit_defs/unrolled_circuits/unified_reduced_machine/src/lib.rs#UnifiedReducedMachineCircuit::table_addition_fn` |
| `ASM-UMWORD-004` | normative | a selected source register is `x0` | `external:REG` | prose | [RV32I register semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html) | — |
| `ASM-UMWORD-005` | normative | active row | `external:DEC`; `external:CONT` | located | aligned unified decoder keys and 32-bit PC continuity at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_pc_bump` |
| `REL-UMWORD-001` | normative | active `LW ∨ SW` | `ASM-UMWORD-001..002` | located | [RV32I effective-address semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified address-limb constraints at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs#apply_unified_mem_word_only_lw_sw_data_path` |
| `REL-UMWORD-002` | normative | active `LW ∨ SW` | `ASM-UMWORD-001..004`; `REL-UMWORD-001` | located | [RV32I word-memory semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); `decision:2026-09-01#emulated-memory-has-no-device-side-effects`; unified ROM/RAM dispatch, alignment, and access copying at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only.rs#apply_unified_mem_word_only_inner`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs#apply_unified_mem_word_only_lw_sw_data_path`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode` |
| `REL-UMWORD-003` | normative | active `LW ∨ SW` | `ASM-UMWORD-005` | located | [RVALP v0.18.4 sequential PC assignment](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified non-overflow enforcement at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_pc_bump` |
