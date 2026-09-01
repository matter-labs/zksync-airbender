# MULDIV: Unsigned multiply/divide family

## Supported operations

- `MUL rd, rs1, rs2`
- `MULHU rd, rs1, rs2`
- `DIVU rd, rs1, rs2`
- `REMU rd, rs1, rs2`

These are the operations exposed by the unrolled `UnsignedMulDivCircuit`. Their
architectural meanings correspond to the official
[RISC-V M extension, Version 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html).
An encoded listed instruction with `rd = x0` is preprocessed to the canonical `NOP`
and is outside this circuit family's active rows.

`MUL` returns the low product word, which is identical for signed and unsigned
two's-complement multiplication. `MULHU` returns the high word of an unsigned product.
`MULH`, `MULHSU`, `DIV`, and `REM` are not supported by this unrolled circuit; therefore
the signed division-overflow case `-2^31 / -1` has no branch in this module.

## Inputs

| Name | Meaning |
|---|---|
| `pc` | current 32-bit program counter |
| `execute` | boolean cycle-activation flag |
| `rs1`, `rs2` | 32-bit values read from the selected source registers |
| `rd` | selected nonzero destination register |
| `op` | one of `MUL`, `MULHU`, `DIVU`, or `REMU` |

Machine words are unsigned integers in `[0, 2^32)`. Source-value consistency follows
from `ASM-MULDIV-003`.

`x <- expression` denotes the cycle's architectural assignment to `x`. The right-hand
side uses pre-cycle values. An assignment must remain in the target's declared domain
unless the expression explicitly says `mod`. Architectural locations not assigned by
the active relation remain unchanged.

## Assumptions

- **ASM-MULDIV-001 — Decoder binding.** `(op, rs1_index, rs2_index, rd)` is the row committed for the current `pc`; active rows have `rd != x0`.
- **ASM-MULDIV-002 — Selector exclusivity.** Exactly one of the four unsigned-family operation selectors is active.
- **ASM-MULDIV-003 — Register consistency.** Register reads and the destination write satisfy the global register-memory argument.
- **ASM-MULDIV-004 — Zero register.** Reading `x0` returns `0`.
- **ASM-MULDIV-005 — PC alignment.** `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-MULDIV-001..005`. Within `execute = 1`, the numbered
> requirements are conjoined. The cases below `REQ-MULDIV-001` are mutually exclusive.

- **`execute = 0`.** Outside this module's active-row scope.
- **`execute = 1`.**
  - **[`REQ-MULDIV-001`] Destination assignment.** The selected case assigns `rd`:
    - **`op = MUL`.**
      `rd <- (rs1 * rs2) mod 2^32`.
    - **`op = MULHU`.**
      `rd <- floor((rs1 * rs2) / 2^32)`.
    - **`op = DIVU`.**
      - **`rs2 = 0`.**
        `rd <- 2^32 - 1`.
      - **`rs2 != 0`.**
        `rd <- floor(rs1 / rs2)`.
    - **`op = REMU`.**
      - **`rs2 = 0`.**
        `rd <- rs1`.
      - **`rs2 != 0`.**
        `rd <- rs1 mod rs2`.
  - **[`REQ-MULDIV-002`] Non-wrapping PC assignment.**
    `pc + 4 < 2^32`;
    `pc <- pc + 4`.

## Derived facts

For a quick structural view of every active row:

- `MUL` gives the same low word whether the operand bit patterns are interpreted as
  signed or unsigned; `MULHU` specifically gives the unsigned high word;
- for `rs2 != 0`, unsigned division has unique values `q` and `r` satisfying
  `rs1 = q * rs2 + r` and `0 <= r < rs2`; `DIVU` assigns `q` and `REMU` assigns `r`;
- for `rs2 = 0`, `DIVU` assigns the all-ones word and `REMU` assigns the dividend;
- `ASM-MULDIV-005` and `REQ-MULDIV-002` imply `pc <= 2^32 - 8` before the
  assignment and `pc <= 2^32 - 4` afterward;
- `ASM-MULDIV-005` and `REQ-MULDIV-002` imply that the assigned `pc` remains divisible
  by four;
- among architectural registers, only `rd` may change by `REQ-MULDIV-001` and the
  assignment convention.

## Metadata

These relations are normative for the stated unsigned unrolled profile. Arithmetic
semantics adopt the official [RISC-V M extension](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html),
with profile selection and circuit boundaries supported by convergent decoder,
constraint, setup, and architecture evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled `UnsignedMulDivCircuit`, unsigned M-extension subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MULDIV-001` | normative | active row | `external:DEC` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm@dfb1b2a8a`; `repo:cs/src/gkr_circuits/mul_div/decoder.rs#DivMulDecoder::define_decoder_subspace@dfb1b2a8a`; current-PC decoder lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; aligned table materialization in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; unsigned-family selection and setup in `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type@dfb1b2a8a` and `repo:circuit_defs/setups/src/unrolled_circuits/mul_div_unsigned_circuit/mod.rs#mul_div_unsigned_circuit_setup@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm`; `symbol:cs/src/gkr_circuits/mul_div/decoder.rs#DivMulDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type`; `symbol:circuit_defs/setups/src/unrolled_circuits/mul_div_unsigned_circuit/mod.rs#mul_div_unsigned_circuit_setup` |
| `ASM-MULDIV-002` | normative | active row | `external:DEC` | located | one-bit family encodings in `repo:cs/src/gkr_circuits/mul_div/decoder.rs#DivMulDecoder::define_decoder_subspace@dfb1b2a8a`; atomic bitmask packing in the active decoder lookup at `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; table materialization at `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; unsigned-family composition and setup at `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type@dfb1b2a8a` and `repo:circuit_defs/setups/src/unrolled_circuits/mul_div_unsigned_circuit/mod.rs#mul_div_unsigned_circuit_setup@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mul_div/decoder.rs#DivMulDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type`; `symbol:circuit_defs/setups/src/unrolled_circuits/mul_div_unsigned_circuit/mod.rs#mul_div_unsigned_circuit_setup` |
| `ASM-MULDIV-003` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner` |
| `ASM-MULDIV-004` | normative | `rs1_index = 0 || rs2_index = 0` | `external:REG` | prose | [RISC-V RV32I register model](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); global register-memory argument | — |
| `ASM-MULDIV-005` | normative | active row | `external:MACH` | located | active decoder lookup includes the cycle-start PC in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; decoder-table keys are `4 * instruction_index` in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; global cycle-state chain | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask` |
| `REQ-MULDIV-001` | normative | active operation row | `ASM-MULDIV-001..004` | located | [RISC-V M extension, Version 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html); `repo:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner` |
| `REQ-MULDIV-002` | normative | active row | 32-bit `pc` input domain | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
