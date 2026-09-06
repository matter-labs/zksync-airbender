# UJUMP: Unified jump, branch, and set-less-than body

> Architectural relation of the reduced unified machine's embedded control-flow and
> comparison body; shared decoding, register state, and cycle continuity are imported.

## Supported operations

- `JAL rd, imm21`
- `JALR rd, rs1, imm12`
- `BEQ rs1, rs2, imm13`
- `BNE rs1, rs2, imm13`
- `BLT rs1, rs2, imm13`
- `BGE rs1, rs2, imm13`
- `BLTU rs1, rs2, imm13`
- `BGEU rs1, rs2, imm13`
- `SLT rd, rs1, rs2`
- `SLTI rd, rs1, imm12`
- `SLTU rd, rs1, rs2`
- `SLTIU rd, rs1, imm12`

Comparisons enter this body only when `rd ≠ x0`; preprocessing maps a comparison
with `rd = x0` to `NOP`. `JAL` and `JALR` retain their control-flow effect when
`rd = x0`.

## Inputs

- `u12 = [0, 2¹²)`, `u13 = [0, 2¹³)`, `u21 = [0, 2²¹)`, and
  `u32 = [0, 2³²)` are unsigned integer domains
- `pc ∈ u32` is the current program counter
- `execute ∈ {0, 1}` activates the unified cycle
- `rs1, rs2 ∈ u32` are register values, not register indexes
- `imm12 ∈ u12` is the encoded I-immediate
- `imm13 ∈ u13` and `imm13 mod 2 = 0` are the decoded B-immediate
- `imm21 ∈ u21` and `imm21 mod 2 = 0` are the decoded J-immediate
- `rd` is the destination register; `rd = x0` is admitted only for `JAL` and `JALR`
- `op` is one of the supported operations
- `sign_extend_12`, `sign_extend_13`, and `sign_extend_21` map the corresponding
  immediate to `u32`
- `s32(x)` interprets `x ∈ u32` as a signed two's-complement integer
- `&` denotes bitwise AND on `u32`
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-UJUMP-001 — Unified decoder authentication.** For an active family-2 row, the unified decoder authenticates one supported `op`, its selected registers, destination, and encoded immediate against the instruction at the current `pc`
- **ASM-UJUMP-002 — Register consistency.** Register reads and any destination write satisfy the global register-memory argument
- **ASM-UJUMP-003 — Zero register.** Reading `x0` returns `0`; writing `x0` preserves `0`
- **ASM-UJUMP-004 — PC alignment.** The active decoder lookup binds `pc` to a table key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle
- **ASM-UJUMP-005 — PC word closure.** The cycle-end PC participates in the global machine-state permutation as a value in `u32`

## Canonical relation tree

> Interpret this tree under `ASM-UJUMP-001..005`. Within `execute = 1`, exactly one
> numbered relation applies

- **`execute = 0`** Outside this body's active-row scope
- **`execute = 1`**
  - **`op ∈ {SLT, SLTI, SLTU, SLTIU}` — [`REL-UJUMP-001`] Comparison assignment**
    - **`op = SLT`**
      `rd ← 1` if `s32(rs1) < s32(rs2)`, otherwise `rd ← 0`
    - **`op = SLTI`**
      `rd ← 1` if `s32(rs1) < s32(sign_extend_12(imm12))`, otherwise `rd ← 0`
    - **`op = SLTU`**
      `rd ← 1` if `rs1 < rs2`, otherwise `rd ← 0`
    - **`op = SLTIU`**
      `rd ← 1` if `rs1 < sign_extend_12(imm12)`, otherwise `rd ← 0`
    - `pc ← (pc + 4) mod 2³²`
  - **`op ∈ {BEQ, BNE, BLT, BGE, BLTU, BGEU}` — [`REL-UJUMP-002`] Conditional branch assignment**
    - `taken ∈ {0, 1}`
    - **`op = BEQ`** `taken ⇔ rs1 = rs2`
    - **`op = BNE`** `taken ⇔ rs1 ≠ rs2`
    - **`op = BLT`** `taken ⇔ s32(rs1) < s32(rs2)`
    - **`op = BGE`** `taken ⇔ s32(rs1) ≥ s32(rs2)`
    - **`op = BLTU`** `taken ⇔ rs1 < rs2`
    - **`op = BGEU`** `taken ⇔ rs1 ≥ rs2`
    - **`taken = 0`**
      `pc ← (pc + 4) mod 2³²`
    - **`taken = 1`**
      `target = (pc + sign_extend_13(imm13)) mod 2³²`
      `target mod 4 = 0`
      `pc ← target`
  - **`op ∈ {JAL, JALR}` — [`REL-UJUMP-003`] Jump assignment**
    - **`rd ≠ x0`**
      `rd ← (pc + 4) mod 2³²`
    - **`rd = x0`** No register changes
    - **`op = JAL`**
      `target = (pc + sign_extend_21(imm21)) mod 2³²`
      `target mod 4 = 0`
      `pc ← target`
    - **`op = JALR`**
      `raw_target = (rs1 + sign_extend_12(imm12)) mod 2³²`
      `target = raw_target − (raw_target mod 2)`
      `target mod 4 = 0`
      `pc ← target`

## Derived facts

- **Comparison result**
  `op ∈ {SLT, SLTI, SLTU, SLTIU} ⇒ rd ∈ {0, 1}`
- **32-bit assignments**
  `rd ∈ u32`
  `pc ∈ u32`
- **PC alignment**
  `pc mod 4 = 0`
- **JALR target alignment**
  `op = JALR ⇒ pc[1:0] = 0`
- **Register effects**
  `op ∈ {BEQ, BNE, BLT, BGE, BLTU, BGEU} ⇒` no register changes
  `op ∈ {SLT, SLTI, SLTU, SLTIU, JAL, JALR} ∧ rd ≠ x0 ⇒` only `rd` may change
  `op ∈ {JAL, JALR} ∧ rd = x0 ⇒` no register changes
  `x0 = 0`

## Implementation conformance

At `dfb1b2a8a`, the not-taken-branch witness default in
`apply_unified_jump_branch_slt_inner` assigns the final-overflow and low-limb-carry
witnesses in the opposite order. For example, `pc = 0x0000fffc` needs low carry `1`
and final overflow `0`, but the default witness supplies `0` and `1`, so witness
generation can fail the low-limb equation for the valid transition in
`REL-UJUMP-002`. This is a prover-completeness implementation defect; it does not
change the specified relation.

This module specifies the unified body directly and does not assert equivalence with
the standalone `JUMP` circuit.

## Metadata

These relations are normative for the reduced unified profile. Ordinary instruction
semantics adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).
The [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate the comparison results, branch predicates, jump targets, link assignments,
and sequential `pc ← pc + 4` behavior. Airbender additionally makes PC arithmetic
explicitly modulo `2³²`, canonicalizes comparisons with `rd = x0` to `NOP`, and makes
a four-byte-aligned taken target a satisfiability condition rather than modeling the
RV32I instruction-address-misaligned exception. The unified body implements these
relations with a reduced conditional-resolution table, separate operand-sign lookup,
family-gated lookup requests, and family-gated destination constraints; those are
implementation adaptations rather than additional architectural behavior.

- spec revision: TBD
- implementation: TBD
- profile: reduced unified machine, embedded family 2

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-UJUMP-001` | normative | active family-2 row | `REQ-UNIFIED-001`; `external:DEC` | located | unified preprocessing and decoder at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs#JumpSltBranchDecoder::define_decoder_subspace` |
| `ASM-UJUMP-002` | normative | active family-2 row | `external:REG` | located | unified register-access resolver and global register-memory argument at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_reduced_machine_inner` |
| `ASM-UJUMP-003` | normative | selected source or destination is `x0` | `external:REG` | located | [RV32I `x0` semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); unified destination constraints | `symbol:cs/src/gkr_circuits/unified_reduced_machine/jump_branch_slt.rs#apply_unified_jump_branch_slt_inner` |
| `ASM-UJUMP-004` | normative | active family-2 row | `external:DEC` | located | aligned unified decoder lookup keys at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_reduced_machine_inner` |
| `ASM-UJUMP-005` | normative | cycle-end state | `REQ-CONT-003`; `REQ-CONT-005` | located | unified cycle-state output and global machine-state permutation at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_reduced_machine_inner`; `symbol:cs/src/definitions/gkr/mod.rs#MachineStatePermutationDescription` |
| `REL-UJUMP-001` | normative | active unified comparison row | `ASM-UJUMP-001..005` | located | [RV32I comparisons](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified family-2 body and lookup tables at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/jump_branch_slt.rs#apply_unified_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table_unified` |
| `REL-UJUMP-002` | normative | active unified conditional-branch row | `ASM-UJUMP-001..005` | located | [RV32I conditional branches](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified family-2 body and lookup tables at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/jump_branch_slt.rs#apply_unified_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table_unified`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table` |
| `REL-UJUMP-003` | normative | active unified `JAL` or `JALR` row | `ASM-UJUMP-001..005` | located | [RV32I `JAL` and `JALR`](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified family-2 body at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/jump_branch_slt.rs#apply_unified_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table` |
