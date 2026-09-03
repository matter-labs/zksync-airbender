# MULDIVU: Unsigned multiply/divide family

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

`MULH`, `MULHSU`, `DIV`, and `REM` are outside this unsigned profile. Their dormant
`SUPPORT_SIGNED = true` decoder and circuit paths are incomplete and are not wired into
the unrolled setup.

## Inputs

- `u32 = [0, 2³²)` is the unsigned 32-bit integer domain
- `pc ∈ u32` is the current program counter
- `execute ∈ {0, 1}` activates the cycle
- `rs1, rs2 ∈ u32` are register values interpreted as unsigned integers
- `rd ≠ x0` is the destination register
- `op` is one of the supported operations
- `⌊x⌋` is the integer floor of `x`
- `≫ (with zero fill)` fills vacated high bits with zero
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-MULDIVU-001 — Decoder authentication.** For an active row, the decoder authenticates exactly one supported `op`, its selected source registers, and `rd` against the instruction at the current `pc`.
- **ASM-MULDIVU-002 — Register consistency.** Register reads and the destination write satisfy the global register-memory argument.
- **ASM-MULDIVU-003 — Zero register.** Reading `x0` returns `0`.
- **ASM-MULDIVU-004 — PC alignment.** The active decoder lookup binds `pc` to a table key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-MULDIVU-001..004`. Within `execute = 1`, the numbered
> relations are conjoined. The cases below `REL-MULDIVU-001` are mutually exclusive.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-MULDIVU-001`] Destination assignment**
    - **`op = MUL`**
      `rd ← (rs1 × rs2) mod 2³²`
    - **`op = MULHU`**
      `rd ← (rs1 × rs2) ≫ 32 (with zero fill)`
    - **`op = DIVU`**
      - **`rs2 = 0`**
        `rd ← 2³² − 1`
      - **`rs2 ≠ 0`**
        `rd ← ⌊rs1 / rs2⌋`
    - **`op = REMU`**
      - **`rs2 = 0`**
        `rd ← rs1`
      - **`rs2 ≠ 0`**
        `rd ← rs1 mod rs2`
  - **[`REL-MULDIVU-002`] Non-wrapping PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

- **Unsigned quotient-remainder identity**
  `rs2 ≠ 0`
  `q = ⌊rs1 / rs2⌋`
  `r = rs1 mod rs2`
  `q, r ∈ u32`
  `rs1 = q × rs2 + r`
  `r < rs2`
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

These relations are normative for the stated unsigned unrolled profile. Arithmetic
semantics adopt the official [RISC-V M extension](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html).
The [RVALP v0.18.4 RV32M chapter](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborates the instruction encodings and the `MUL` low-word assignment; the official
M-extension text controls the remaining arithmetic and exceptional cases. Profile
selection and circuit boundaries are supported by convergent decoder, constraint,
setup, and architecture evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: TBD
- implementation: TBD
- profile: unrolled `UnsignedMulDivCircuit`, unsigned M-extension subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MULDIVU-001` | normative | active row | `external:DEC` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm@dfb1b2a8a`; `repo:cs/src/gkr_circuits/mul_div/decoder.rs#DivMulDecoder::define_decoder_subspace@dfb1b2a8a`; current-PC decoder lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; unsigned-family selection and setup in `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type@dfb1b2a8a` and `repo:circuit_defs/setups/src/unrolled_circuits/mul_div_unsigned_circuit/mod.rs#mul_div_unsigned_circuit_setup@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm`; `symbol:cs/src/gkr_circuits/mul_div/decoder.rs#DivMulDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type`; `symbol:circuit_defs/setups/src/unrolled_circuits/mul_div_unsigned_circuit/mod.rs#mul_div_unsigned_circuit_setup` |
| `ASM-MULDIVU-002` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner` |
| `ASM-MULDIVU-003` | normative | a selected source register is `x0` | `external:REG` | prose | [RISC-V RV32I register model](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); global register-memory argument | — |
| `ASM-MULDIVU-004` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; decoder lookup construction in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REL-MULDIVU-001` | normative | active operation row | `ASM-MULDIVU-001..003` | located | [RISC-V M multiplication](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html#mult-ops); [RISC-V M division](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html#11-1-2-division-operations); [division edge cases](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html#divby0); [RVALP v0.18.4 RV32M chapter](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf) for encodings and `MUL`; `repo:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mul_div/circuit.rs#apply_mul_div_inner` |
| `REL-MULDIVU-002` | normative | active row | 32-bit `pc` input domain | located | [RVALP v0.18.4 sequential PC assignment](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); non-overflow enforcement at `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
