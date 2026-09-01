# MEMSUB: Subword memory family

## Supported operations

- `LB rd, imm12(rs1)`
- `LBU rd, imm12(rs1)`
- `LH rd, imm12(rs1)`
- `LHU rd, imm12(rs1)`
- `SB rs2, imm12(rs1)`
- `SH rs2, imm12(rs1)`

The six data transformations below follow the official
[RV32I load/store specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html),
with Airbender's emulated-machine boundary. A load with `rd = x0` is rewritten to the
canonical `NOP` before this family is selected, so no access at its original effective
address enters the memory argument. The inspected machine has no MMIO or external
memory-side-effect channel. Stores retain their memory effect.

## Inputs

| Name | Meaning |
|---|---|
| `pc` | current 32-bit program counter |
| `execute` | boolean cycle-activation flag |
| `rs1`, `rs2` | 32-bit values read from the selected source registers |
| `imm12` | encoded 12-bit I- or S-immediate |
| `rd` | selected destination register for a load |
| `op` | one of `LB`, `LBU`, `LH`, `LHU`, `SB`, or `SH` |
| `M[w]` | 32-bit little-endian memory word at four-byte-aligned byte address `w` |

Let `ROM_LIMIT = 2^22`. For a 32-bit word `x`:

- `byte(x, i) = floor(x / 2^(8i)) mod 2^8`, for `i in {0, 1, 2, 3}`;
- `half(x, i) = floor(x / 2^(8i)) mod 2^16`, for `i in {0, 2}`;
- `replace8(x, i, y)` replaces byte `i` of `x` by `y mod 2^8`;
- `replace16(x, i, y)` replaces bytes `i` and `i + 1` of `x` by
  `y mod 2^16`.

`sign_extend_n` and `zero_extend_n` produce the corresponding 32-bit value.
`x <- expression` denotes the cycle's architectural assignment to `x`; its right-hand
side uses pre-cycle values. Architectural locations not assigned by the active
relation remain unchanged.

## Assumptions

- **ASM-MEMSUB-001 — Decoder binding.** `(op, rs1_index, rs2_index, rd, sign_extend_12(imm12))` is the row committed for the current `pc`; `imm12` uses the instruction's I- or S-immediate encoding.
- **ASM-MEMSUB-002 — Selector exclusivity.** The committed flag combination selects exactly one supported subword-memory operation.
- **ASM-MEMSUB-003 — Register and RAM consistency.** Register reads, load writes, and mutable-RAM reads or writes satisfy the global memory argument, including `x0` semantics and its admitted mutable-address domain.
- **ASM-MEMSUB-004 — ROM binding.** For `w < ROM_LIMIT`, `M[w]` is the raw encoded program-image word at index `w / 4`, or `ROM_PADDING_OPCODE = 0` when that index is beyond the supplied image. The subword ROM tables authenticate extraction from this word.
- **ASM-MEMSUB-005 — PC alignment.** `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-MEMSUB-001..005`. Within `execute = 1`, the
> numbered requirements are conjoined. The cases below `REQ-MEMSUB-001` are
> mutually exclusive.

- **`execute = 0`.** Outside this module's active-row scope.
- **`execute = 1`.**
  - **[`REQ-MEMSUB-001`] Effective address and subword assignment.** Let
    `a = (rs1 + sign_extend_12(imm12)) mod 2^32`, `w = a - (a mod 4)`, and
    `o = a mod 4`. The selected case assigns:
    - **`op = LB`.**
      `rd <- sign_extend_8(byte(M[w], o))`.
    - **`op = LBU`.**
      `rd <- zero_extend_8(byte(M[w], o))`.
    - **`op = LH`.**
      `o mod 2 = 0`;
      `rd <- sign_extend_16(half(M[w], o))`.
    - **`op = LHU`.**
      `o mod 2 = 0`;
      `rd <- zero_extend_16(half(M[w], o))`.
    - **`op = SB`.**
      `w >= ROM_LIMIT`;
      `M[w] <- replace8(M[w], o, rs2)`.
    - **`op = SH`.**
      `o mod 2 = 0`;
      `w >= ROM_LIMIT`;
      `M[w] <- replace16(M[w], o, rs2)`.
  - **[`REQ-MEMSUB-002`] Non-wrapping PC assignment.**
    `pc + 4 < 2^32`;
    `pc <- pc + 4`.

## Derived facts

For a quick structural view of every active row:

- effective-address addition wraps modulo `2^32` by `REQ-MEMSUB-001`;
- byte operations accept every byte offset, while halfword operations accept only
  offsets `0` and `2`, so a selected subword never crosses `M[w]`;
- signed loads fill all bits above the selected subword with its sign bit; unsigned
  loads fill them with zero;
- stores preserve every unselected byte and cannot modify the fixed ROM region;
- among registers and memory, a load changes at most `rd`, while a store changes at
  most `M[w]`, by `REQ-MEMSUB-001` and the assignment convention;
- `ASM-MEMSUB-005` and `REQ-MEMSUB-002` imply `pc <= 2^32 - 8` before the
  assignment, `pc <= 2^32 - 4` afterward, and continued four-byte alignment.

## Metadata

These relations are normative for the stated unrolled profile. Load/store semantics
adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html),
with Airbender's ROM boundary and discarded-load behavior supported by explicit
project decisions and convergent decoder, constraint, table, and memory-argument
evidence checked at `matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled `mem_subword_only`, full-machine subword-memory subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MEMSUB-001` | normative | active row | `external:DEC` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/mem_subword_only/decoder.rs#define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/mem_subword_only/decoder.rs#define_decoder_subspace` |
| `ASM-MEMSUB-002` | normative | active row | `external:DEC` | located | `repo:cs/src/gkr_circuits/mem_subword_only/decoder.rs#define_decoder_subspace@dfb1b2a8a`; authenticated decoder lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_subword_only/decoder.rs#define_decoder_subspace`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `ASM-MEMSUB-003` | normative | active row | `external:REG`; `external:MEM` | located | `repo:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner@dfb1b2a8a`; global memory argument | `symbol:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner`; `symbol:cs/src/cs/circuit_impl.rs#request_mem_access` |
| `ASM-MEMSUB-004` | normative | `w < ROM_LIMIT` | `external:MEM` | located | raw bytecode is passed by `repo:circuit_defs/unrolled_circuits/load_store_subword_only/src/lib.rs#LoadStoreSubwordOnlyCircuit@dfb1b2a8a`; `repo:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2@dfb1b2a8a`; `repo:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE@dfb1b2a8a`; ROM extraction tables | `symbol:circuit_defs/unrolled_circuits/load_store_subword_only/src/lib.rs#LoadStoreSubwordOnlyCircuit`; `symbol:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2`; `symbol:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE`; `symbol:cs/src/tables/rom_related.rs#create_load_byte_from_rom_table`; `symbol:cs/src/tables/rom_related.rs#create_load_halfword_from_rom_table` |
| `ASM-MEMSUB-005` | normative | active row | `external:MACH` | located | aligned authenticated decoder keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; initial PC and global machine-state wiring | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:common_constants/src/lib.rs#INITIAL_PC`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REQ-MEMSUB-001` | normative | active operation row | `ASM-MEMSUB-001..004` | located | [RV32I load/store semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); `repo:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner@dfb1b2a8a`; `repo:cs/src/tables/memory_opcode_related.rs#create_load_byte_signextend_table@dfb1b2a8a`; `repo:cs/src/tables/memory_opcode_related.rs#create_load_halfword_signextend_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner`; `symbol:cs/src/tables/memory_opcode_related.rs#create_load_byte_signextend_table`; `symbol:cs/src/tables/memory_opcode_related.rs#create_load_halfword_signextend_table`; `symbol:cs/src/tables/memory_opcode_related.rs#create_store_byte_source_contribution_table`; `symbol:cs/src/tables/memory_opcode_related.rs#create_store_byte_existing_contribution_table` |
| `REQ-MEMSUB-002` | normative | active row | 32-bit `pc` input domain | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
