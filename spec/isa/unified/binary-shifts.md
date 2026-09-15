# UBSHIFT: Unified bitwise and shift body

> Bitwise and shift relations embedded in the reduced unified executor. This module
> does not assert equivalence with the standalone `BSHIFT` circuit.

`*` marks the custom xor-rotate relation and decoder boundary whose intendedness is
supported only by the current implementation.

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
- `MOP.R.16 rd, rs1` (`XORROT16`)
- `MOP.R.12 rd, rs1` (`XORROT12`)
- `MOP.R.8 rd, rs1` (`XORROT8`)
- `MOP.R.7 rd, rs1` (`XORROT7`)

The unified decoder admits these operations only when `rd ≠ x0`. Preprocessing
canonicalizes an ordinary listed instruction with `rd = x0` to `NOP`, which is
outside this module.

## Inputs

- `u5 = [0, 2⁵)`, `u12 = [0, 2¹²)`, and `u32 = [0, 2³²)` are unsigned integer
  domains
- `pc ∈ u32` is the current program counter
- `execute ∈ {0, 1}` activates the cycle
- `rs1, rs2 ∈ u32` are register values, not register indexes
- `imm12 ∈ u12` is the encoded immediate
- `r ∈ u5` is the index encoded by `MOP.R.r`
- `rd ≠ x0` is the destination register
- `op` is one of the supported operations
- `x[4:0]` is the inclusive bit slice from bit 4 through bit 0
- `sign_extend_12(x)` is the sign extension of `x ∈ u12` to `u32`
- `&`, `|`, and `^` denote bitwise AND, OR, and XOR on `u32`
- `≪` denotes left shift
- `≫ (with zero fill)` fills vacated high bits with zero
- `≫ (with sign fill)` fills vacated high bits with the original bit `x[31]`
- `x ⋙ r` cyclically rotates the 32-bit word `x` right by `r` bits
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-UBSHIFT-001 — Ordinary decoder authentication.** For an active ordinary row,
  the unified decoder authenticates exactly one standard supported `op`, its selected
  source registers, `rd`, and its encoded immediate against the instruction at `pc`.
- **ASM-UBSHIFT-002* — Xor-rotate decoder boundary.** For an active `MOP.R.r`
  (`XORROT-r`) row, the unified decoder authenticates `rs1`, selects the pre-cycle
  value of `rd` as the second source, and authenticates
  `r ∈ {16, 12, 8, 7}`.
- **ASM-UBSHIFT-003 — Register consistency.** Register reads and the destination write
  satisfy the global register-memory argument.
- **ASM-UBSHIFT-004 — Zero register.** Reading `x0` returns `0`.
- **ASM-UBSHIFT-005 — PC alignment.** The active decoder lookup binds `pc` to a table
  key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-UBSHIFT-001..005`. Within `execute = 1`, the
> applicable destination relation and `REL-UBSHIFT-003` are conjoined.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-UBSHIFT-001`] Standard destination assignment**
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
  - **[`REL-UBSHIFT-002*`] Custom xor-rotate assignment**
    - **`op = MOP.R.r` (`XORROT-r`), `r ∈ {16, 12, 8, 7}`**
      `rd ← (rs1 ^ rd) ⋙ r`
  - **[`REL-UBSHIFT-003`] Non-wrapping PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

- **Shift amounts**
  `rs2[4:0] ∈ u5`
  `imm12[4:0] ∈ u5`
- **Xor-rotate amounts**
  `r ∈ {16, 12, 8, 7} ⊂ u5`
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

## Open boundary

- **GAP-UBSHIFT-001 — Custom xor-rotate adoption.** Adopt or replace the
  `XORROT-r` redefinition of `MOP.R.r` and the exact rotation set
  `{16, 12, 8, 7}`. The current relation is independently enforced by decoder,
  lookup-table, reconstruction, and decoder-test code, but has no adopted semantic
  project-design reference.

## Metadata

Standard operation relations are normative for this profile. They adopt the official
[RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html),
and the [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate their destination and sequential-PC assignments. The custom xor-rotate
carrier follows the official
[Zimop syntax](https://docs.riscv.org/reference/isa/unpriv/zimop.html); its Airbender
relation remains provisional pending `GAP-UBSHIFT-001`.

- spec revision: TBD
- implementation: TBD
- profile: reduced unified machine, embedded bitwise and shift body

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-UBSHIFT-001` | normative | active ordinary row | `external:DEC`; `REQ-UNIFIED-001` | located | ordinary decoder normalization and unified dispatch at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace` |
| `ASM-UBSHIFT-002` | provisional | active `MOP.R.r` row with `r ∈ {16, 12, 8, 7}` | `external:DEC`; `REQ-UNIFIED-001`; `GAP-UBSHIFT-001` | checked | [Zimop carrier syntax](https://docs.riscv.org/reference/isa/unpriv/zimop.html); xor-rotate preprocessing, decoder dispatch, and decoder rotation-map test at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace`; `check:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#tests::xor_rot_unified_only` |
| `ASM-UBSHIFT-003` | normative | active row | `external:REG` | located | unified shared register-access allocation and global register-memory argument at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core` |
| `ASM-UBSHIFT-004` | normative | a selected source register is `x0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-UBSHIFT-005` | normative | active row | `external:DEC` | located | aligned unified decoder-table keys at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REL-UBSHIFT-001` | normative | active ordinary bitwise/shift row | `ASM-UBSHIFT-001`, `ASM-UBSHIFT-003..004` | located | [RV32I bitwise and shift semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified byte lookup and reconstruction path at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/binary_shifts.rs#apply_unified_binary_shifts_inner`; `symbol:cs/src/tables/binops.rs#create_wide_xor_table`; `symbol:cs/src/tables/binops.rs#create_wide_or_table`; `symbol:cs/src/tables/binops.rs#create_wide_and_table`; `symbol:cs/src/tables/shift_opcode_related.rs#create_shift_implementation_table` |
| `REL-UBSHIFT-002` | provisional | active `MOP.R.r` row with `r ∈ {16, 12, 8, 7}` | `ASM-UBSHIFT-002..003`; `GAP-UBSHIFT-001` | located | unified xor-rotate lookup and cyclic reconstruction at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/binary_shifts.rs#apply_unified_binary_shifts_inner`; `symbol:cs/src/tables/binops.rs#create_xor_rotate_table` |
| `REL-UBSHIFT-003` | normative | active unified bitwise/shift row | `ASM-UBSHIFT-005`; 32-bit `pc` input domain | located | [RVALP v0.18.4 sequential PC assignment](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified non-Family-2 PC bump and output-limb range checks at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_pc_bump` |
| `GAP-UBSHIFT-001` | open | — | affects `ASM-UBSHIFT-002`, `REL-UBSHIFT-002`; owner: human | — | official Zimop defines the carrier, but no adopted project-design reference defines the Airbender `XORROT-r` relation | — |
