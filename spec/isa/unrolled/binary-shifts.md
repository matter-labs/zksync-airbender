# BSHIFT: Bitwise and shift family

## Supported operations

- `AND rd, rs1, rs2`
- `ANDI rd, rs1, imm12`
- `OR rd, rs1, rs2`
- `ORI rd, rs1, imm12`
- `XOR rd, rs1, rs2`
- `XORI rd, rs1, imm12`
- `SLL rd, rs1, rs2`
- `SLLI rd, rs1, imm12[4:0]`
- `SRL rd, rs1, rs2`
- `SRLI rd, rs1, imm12[4:0]`
- `SRA rd, rs1, rs2`
- `SRAI rd, rs1, imm12[4:0]`

The standalone family admits these operations only when `rd ≠ x0`. The preprocessor
canonicalizes a listed instruction with `rd = x0` to `NOP`, which is outside this
module.

## Inputs

- `u5 = [0, 2⁵)`, `u12 = [0, 2¹²)`, and `u32 = [0, 2³²)` are unsigned integer
  domains
- `pc ∈ u32` is the current program counter
- `execute ∈ {0, 1}` activates the cycle
- `rs1, rs2 ∈ u32` are register values, not register indexes
- `imm12 ∈ u12` is the encoded immediate
- `rd ≠ x0` is the destination register
- `op` is one of the supported operations
- `x[4:0]` is the inclusive bit slice from bit 4 through bit 0
- `sign_extend_12(x)` is the sign extension of `x ∈ u12` to `u32`
- `&`, `|`, and `^` denote bitwise AND, OR, and XOR on `u32`
- `≪` denotes left shift
- `≫ (with zero fill)` fills vacated high bits with zero
- `≫ (with sign fill)` fills vacated high bits with the original bit `x[31]`
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-BSHIFT-001 — Decoder authentication.** For an active row, the decoder authenticates exactly one supported `op`, its selected source registers, `rd`, and its encoded immediate field against the instruction at the current `pc`.
- **ASM-BSHIFT-002 — Register consistency.** Register reads and the destination write satisfy the global register-memory argument.
- **ASM-BSHIFT-003 — Zero register.** Reading `x0` returns `0`.
- **ASM-BSHIFT-004 — PC alignment.** The active decoder lookup binds `pc` to a table key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-BSHIFT-001..004`. Within `execute = 1`, the numbered
> relations are conjoined. The twelve operation cases below
> `REL-BSHIFT-001` are mutually exclusive.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-BSHIFT-001`] Destination assignment**
    - **`op = AND`**
      `rd ← rs1 & rs2`
    - **`op = ANDI`**
      `rd ← rs1 & sign_extend_12(imm12)`
    - **`op = OR`**
      `rd ← rs1 | rs2`
    - **`op = ORI`**
      `rd ← rs1 | sign_extend_12(imm12)`
    - **`op = XOR`**
      `rd ← rs1 ^ rs2`
    - **`op = XORI`**
      `rd ← rs1 ^ sign_extend_12(imm12)`
    - **`op = SLL`**
      `rd ← (rs1 ≪ rs2[4:0]) mod 2³²`
    - **`op = SLLI`**
      `rd ← (rs1 ≪ imm12[4:0]) mod 2³²`
    - **`op = SRL`**
      `rd ← rs1 ≫ rs2[4:0] (with zero fill)`
    - **`op = SRLI`**
      `rd ← rs1 ≫ imm12[4:0] (with zero fill)`
    - **`op = SRA`**
      `rd ← rs1 ≫ rs2[4:0] (with sign fill)`
    - **`op = SRAI`**
      `rd ← rs1 ≫ imm12[4:0] (with sign fill)`
  - **[`REL-BSHIFT-002`] Non-wrapping PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

- **Shift amounts**
  `rs2[4:0] ∈ u5`
  `imm12[4:0] ∈ u5`
- **32-bit assignments**
  `rd ∈ u32`
  `pc ∈ u32`
- **PC range**
  `pc ≤ 2³² − 8` before assignment
  `pc ≤ 2³² − 4` after assignment
- **PC alignment**
  `pc mod 4 = 0`
- **Register effects**
  Only `rd` may change

## Metadata

These relations are normative for the stated unrolled profile. Ordinary instruction
semantics adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html);
the [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate each destination assignment and `pc ← pc + 4`. Operand normalization
and circuit boundaries are supported by convergent decoder, constraint, table, and
architecture evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-09-02.1`
- profile: unrolled `shift_binop`, ordinary bitwise and shift subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-BSHIFT-001` | normative | active row | `external:DEC` | located | program preprocessing and normalized family decoder at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm`; `symbol:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#modify_immediate_for_binary_ops`; `symbol:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#ShiftBinaryDecoder::define_decoder_subspace` |
| `ASM-BSHIFT-002` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner` |
| `ASM-BSHIFT-003` | normative | a selected source register is `x0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-BSHIFT-004` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; decoder lookup construction in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REL-BSHIFT-001` | normative | active operation row | `ASM-BSHIFT-001..003` | located | [RV32I bitwise and shift semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `repo:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_and_table@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_or_table@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_xor_table@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_sign_extension_byte_table@dfb1b2a8a`; `repo:cs/src/tables/shift_opcode_related.rs#create_truncate_shift_amount_and_range_check_8_table@dfb1b2a8a`; `repo:cs/src/tables/shift_opcode_related.rs#create_shift_implementation_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner`; `symbol:cs/src/tables/binops.rs#create_and_table`; `symbol:cs/src/tables/binops.rs#create_or_table`; `symbol:cs/src/tables/binops.rs#create_xor_table`; `symbol:cs/src/tables/binops.rs#create_sign_extension_byte_table`; `symbol:cs/src/tables/shift_opcode_related.rs#create_truncate_shift_amount_and_range_check_8_table`; `symbol:cs/src/tables/shift_opcode_related.rs#create_shift_implementation_table` |
| `REL-BSHIFT-002` | normative | active row | 32-bit `pc` input domain | located | [RVALP v0.18.4 sequential PC assignment](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); non-overflow enforcement at `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
