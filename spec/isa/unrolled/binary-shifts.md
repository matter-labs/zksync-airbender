# BSHIFT: Bitwise and shift family

## Supported operations

- `AND rd, rs1, rs2`
- `ANDI rd, rs1, imm12`
- `OR rd, rs1, rs2`
- `ORI rd, rs1, imm12`
- `XOR rd, rs1, rs2`
- `XORI rd, rs1, imm12`
- `SLL rd, rs1, rs2`
- `SLLI rd, rs1, shamt5`
- `SRL rd, rs1, rs2`
- `SRLI rd, rs1, shamt5`
- `SRA rd, rs1, rs2`
- `SRAI rd, rs1, shamt5`

The standalone family admits these operations only when `rd != x0`. The preprocessor
canonicalizes a listed instruction with `rd = x0` to `NOP`, which is outside this
module.

## Inputs

| Name | Meaning |
|---|---|
| `pc` | current 32-bit program counter |
| `execute` | boolean cycle-activation flag |
| `rs1`, `rs2` | 32-bit values read from the selected source registers |
| `imm12` | encoded 12-bit immediate for `ANDI`, `ORI`, or `XORI` |
| `shamt5` | encoded five-bit immediate shift amount |
| `rhs` | normalized 32-bit bitwise operand, or shift amount in `[0, 32)` |
| `rd` | selected destination register, other than `x0` |
| `class` | one of `AND`, `OR`, `XOR`, `SLL`, `SRL`, or `SRA` |

Machine words are 32-bit values. `signed32(x)` reinterprets the same 32 bits as an
integer in `[-2^31, 2^31)`. Source-value consistency follows from `ASM-BSHIFT-003`.

`x <- expression` denotes the cycle's architectural assignment to `x`. The right-hand
side uses pre-cycle values. An assignment must remain in the target's declared domain
unless the expression explicitly says `mod`. Architectural locations not assigned by
the active relation remain unchanged.

## Assumptions

- **ASM-BSHIFT-001 — Decoder binding and normalization.** The row committed for the
  current `pc` binds `(rs1_index, rs2_index, rd, imm, funct3, selector_bits)`.
  The selector and `funct3` fields denote one of the six normalized classes. Together
  with the authenticated register reads from `ASM-BSHIFT-003`, the row determines
  `rhs` as follows:
  - `AND`, `OR`, and `XOR` use the corresponding class and `rhs = rs2`;
  - `ANDI`, `ORI`, and `XORI` use the corresponding class. If
    `v = sign_extend_12(imm12)`, the decoder stores
    `imm = modify_immediate_for_binary_ops(v)`, where
    `modify_immediate_for_binary_ops(v) = (v & 0xff) | (((v >> 8) & 0xff) << 16)`.
    The circuit sign-extends the stored second byte and reconstructs `rhs = v`;
  - `SLL`, `SRL`, and `SRA` use the corresponding class and `rhs = rs2 mod 32`;
  - `SLLI`, `SRLI`, and `SRAI` use the corresponding class, store `imm = shamt5`,
    and set `rhs = shamt5`.
  The committed row contains no separate register/immediate mnemonic tag after this
  normalization.
- **ASM-BSHIFT-002 — Selector exclusivity.** Exactly one of the binary-operation and shift selectors is active.
- **ASM-BSHIFT-003 — Register consistency.** Register reads and the destination write satisfy the global register-memory argument.
- **ASM-BSHIFT-004 — Zero register.** Reading `x0` returns `0`.
- **ASM-BSHIFT-005 — PC alignment.** The active decoder lookup binds `pc` to a table
  key of the form `4 * i`; therefore `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-BSHIFT-001..005`. Within `execute = 1`, the numbered
> requirements are conjoined. The six normalized-class cases below
> `REQ-BSHIFT-001` are mutually exclusive.

- **`execute = 0`.** Outside this module's active-row scope.
- **`execute = 1`.**
  - **[`REQ-BSHIFT-001`] Destination assignment.** The selected case assigns `rd`:
    - **`class = AND`.**
      `rd <- rs1 & rhs`.
    - **`class = OR`.**
      `rd <- rs1 | rhs`.
    - **`class = XOR`.**
      `rd <- rs1 ^ rhs`.
    - **`class = SLL`.**
      `rd <- (rs1 << rhs) mod 2^32`.
    - **`class = SRL`.**
      `rd <- rs1 >> rhs`, with zero fill.
    - **`class = SRA`.**
      `rd <- signed32(rs1) >> rhs`, reinterpreted as a 32-bit word.
  - **[`REQ-BSHIFT-002`] Non-wrapping PC assignment.**
    `pc + 4 < 2^32`;
    `pc <- pc + 4`.

## Derived facts

For a quick structural view of every active row:

- register shift amounts depend only on the low five bits of `rs2` by
  `ASM-BSHIFT-001` and `REQ-BSHIFT-001`;
- every destination assignment remains a 32-bit word by `REQ-BSHIFT-001` and the
  register word domain;
- `ASM-BSHIFT-005` and `REQ-BSHIFT-002` imply `pc <= 2^32 - 8` before the
  assignment and `pc <= 2^32 - 4` afterward;
- `ASM-BSHIFT-005` and `REQ-BSHIFT-002` imply that the assigned `pc` remains divisible
  by four;
- among registers, at most `rd` changes by `REQ-BSHIFT-001` and the assignment
  convention.

## Metadata

These relations are normative for the stated unrolled profile. Ordinary instruction
semantics adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html);
operand normalization and circuit boundaries are supported by convergent decoder,
constraint, table, and architecture evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled `shift_binop`, ordinary bitwise and shift subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-BSHIFT-001` | normative | active row | `external:DEC`; depends `ASM-BSHIFT-003` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm@dfb1b2a8a`; `repo:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#modify_immediate_for_binary_ops@dfb1b2a8a`; `repo:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#ShiftBinaryDecoder::define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm`; `symbol:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#modify_immediate_for_binary_ops`; `symbol:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#ShiftBinaryDecoder::define_decoder_subspace` |
| `ASM-BSHIFT-002` | normative | active row | `external:DEC` | located | `repo:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#ShiftBinaryDecoder::define_decoder_subspace@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#ShiftBinaryDecoder::define_decoder_subspace` |
| `ASM-BSHIFT-003` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner` |
| `ASM-BSHIFT-004` | normative | `rs_index = 0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-BSHIFT-005` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; decoder lookup construction in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REQ-BSHIFT-001` | normative | active operation row | `ASM-BSHIFT-001..004` | located | `repo:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_and_table@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_or_table@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_xor_table@dfb1b2a8a`; `repo:cs/src/tables/binops.rs#create_sign_extension_byte_table@dfb1b2a8a`; `repo:cs/src/tables/shift_opcode_related.rs#create_truncate_shift_amount_and_range_check_8_table@dfb1b2a8a`; `repo:cs/src/tables/shift_opcode_related.rs#create_shift_implementation_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/binary_shifts_family/circuit.rs#apply_shift_binop_inner`; `symbol:cs/src/tables/binops.rs#create_and_table`; `symbol:cs/src/tables/binops.rs#create_or_table`; `symbol:cs/src/tables/binops.rs#create_xor_table`; `symbol:cs/src/tables/binops.rs#create_sign_extension_byte_table`; `symbol:cs/src/tables/shift_opcode_related.rs#create_truncate_shift_amount_and_range_check_8_table`; `symbol:cs/src/tables/shift_opcode_related.rs#create_shift_implementation_table` |
| `REQ-BSHIFT-002` | normative | active row | 32-bit `pc` input domain | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
