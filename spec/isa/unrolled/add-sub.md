# ADD: Integer add/subtract family

## Supported operations

- `ADD rd, rs1, rs2`
- `ADDI rd, rs1, imm12`
- `LUI rd, imm20`
- `SUB rd, rs1, rs2`
- `AUIPC rd, imm20`
- `NOP`

The preprocessor canonicalizes any listed destination-writing instruction with
`rd = x0` to the `NOP` row.

## Inputs

- `u12 = [0, 2¹²)`, `u20 = [0, 2²⁰)`, and `u32 = [0, 2³²)` are unsigned integer
  domains
- `pc ∈ u32` is the current program counter
- `execute ∈ {0, 1}` activates the cycle
- `rs1, rs2 ∈ u32` are register values, not register indexes
- `imm12 ∈ u12` and `imm20 ∈ u20` are encoded immediate fields
- `rd` is the destination register
- `op` is one of `ADD`, `ADDI`, `LUI`, `SUB`, `AUIPC`, or `NOP`
- `sign_extend_12(x)` is the sign extension of `x ∈ u12` to `u32`
- `x ≪ n` shifts `x` left by `n` bits
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-ADD-001 — Decoder authentication.** For an active row, the decoder authenticates exactly one supported `op`, its selected source registers, `rd`, and its encoded immediate field against the instruction at the current `pc`.
- **ASM-ADD-002 — Register consistency.** Register reads and the destination write satisfy the global register-memory argument.
- **ASM-ADD-003 — Zero register.** Reading `x0` returns `0`; assigning to `x0` preserves `0`.
- **ASM-ADD-004 — PC alignment.** The active decoder lookup binds `pc` to a table key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-ADD-001..004`. Within `execute = 1`, the numbered
> relations are conjoined. The cases below `REL-ADD-001` are mutually
> exclusive.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-ADD-001`] Destination assignment**
    - **`op = ADD`**
      `rd ← (rs1 + rs2) mod 2³²`
    - **`op = ADDI`**
      `rd ← (rs1 + sign_extend_12(imm12)) mod 2³²`
    - **`op = LUI`**
      `rd ← imm20 ≪ 12`
    - **`op = SUB`**
      `rd ← (rs1 − rs2) mod 2³²`
    - **`op = AUIPC`**
      `rd ← (pc + (imm20 ≪ 12)) mod 2³²`
    - **`op = NOP`**
      `rd = x0`
      `rd ← 0`
  - **[`REL-ADD-002`] Non-wrapping PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

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
  `x0 = 0`

## Metadata

These relations are normative for the stated unrolled profile. Ordinary instruction
semantics adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html);
the [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate the ordinary destination assignments and `pc ← pc + 4`. Canonical NOP
routing and non-wrapping PC enforcement are Airbender-specific boundaries supported
by project decisions and convergent constraint and architecture evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-09-02.1`
- profile: unrolled `add_sub_lui_auipc_mop`, ordinary integer subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-ADD-001` | normative | active row | `external:DEC` | located | program preprocessing and normalized family decoder at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace` |
| `ASM-ADD-002` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `ASM-ADD-003` | normative | a selected source or destination register is `x0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-ADD-004` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; active current-PC lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REL-ADD-001` | normative | active operation row | `ASM-ADD-001..003` | located | [RV32I integer-register and upper-immediate semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `REL-ADD-002` | normative | active row | 32-bit `pc` input domain | located | [RVALP v0.18.4 sequential PC assignment](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); non-overflow enforcement at `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
