# JUMP: Jump, branch, and set-less-than family

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

The standalone family admits comparison operations only when `rd ≠ x0`. The
preprocessor canonicalizes a comparison with `rd = x0` to `NOP`, which is outside
this module. `JAL` and `JALR` retain their control-flow effect when `rd = x0`.

## Inputs

- `u12 = [0, 2¹²)`, `u13 = [0, 2¹³)`, `u21 = [0, 2²¹)`, and
  `u32 = [0, 2³²)` are unsigned integer domains
- `pc ∈ u32` is the current program counter
- `execute ∈ {0, 1}` activates the cycle
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

- **ASM-JUMP-001 — Decoder authentication.** For an active row, the decoder authenticates one supported `op`, its selected registers, destination, and encoded immediate against the instruction at the current `pc`. Preprocessing may identify register and immediate comparison forms only when their normalized operands give the same relation.
- **ASM-JUMP-002 — Register consistency.** Register reads and any destination write satisfy the global register-memory argument.
- **ASM-JUMP-003 — Zero register.** Reading `x0` returns `0`; writing `x0` preserves `0`.
- **ASM-JUMP-004 — PC alignment.** The active decoder lookup binds `pc` to a table key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle.
- **ASM-JUMP-005 — PC word closure.** The cycle-end PC participates in the global machine-state permutation as a value in `u32`.

## Canonical relation tree

> Interpret this tree under `ASM-JUMP-001..005`. Within `execute = 1`, exactly one
> numbered relation applies. Operation cases within a relation are mutually
> exclusive.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **`op ∈ {SLT, SLTI, SLTU, SLTIU}` — [`REL-JUMP-001`] Comparison assignment**
    - **`op = SLT`**
      `rd ← 1` if `s32(rs1) < s32(rs2)`, otherwise `rd ← 0`
    - **`op = SLTI`**
      `rd ← 1` if `s32(rs1) < s32(sign_extend_12(imm12))`, otherwise `rd ← 0`
    - **`op = SLTU`**
      `rd ← 1` if `rs1 < rs2`, otherwise `rd ← 0`
    - **`op = SLTIU`**
      `rd ← 1` if `rs1 < sign_extend_12(imm12)`, otherwise `rd ← 0`
    - `pc ← (pc + 4) mod 2³²`
  - **`op ∈ {BEQ, BNE, BLT, BGE, BLTU, BGEU}` — [`REL-JUMP-002`] Conditional branch assignment**
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
  - **`op ∈ {JAL, JALR}` — [`REL-JUMP-003`] Jump assignment**
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
`apply_jump_branch_slt_inner` assigns the final-overflow and low-limb-carry witnesses
in the opposite order. For example, `pc = 0x0000fffc` needs low carry `1` and final
overflow `0`, but the default witness supplies `0` and `1`, so witness generation can
fail the low-limb equation for the valid transition in `REL-JUMP-002`. This is a
prover-completeness implementation defect; it does not change the specified relation.

## Metadata

These relations are normative for the stated unrolled profile. Ordinary instruction
semantics adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).
The [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate the comparison results, branch predicates, jump targets, link assignments,
and sequential `pc ← pc + 4` behavior. Airbender additionally makes PC arithmetic
explicitly modulo `2³²`, canonicalizes comparison instructions with `rd = x0` to
`NOP`, and makes a four-byte-aligned taken target a satisfiability condition rather
than modeling the RV32I instruction-address-misaligned exception. These profile
details are supported by convergent preprocessing, decoder, constraint, table, and
architecture evidence checked at `matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-09-02.1`
- profile: unrolled `jump_branch_slt_family`, ordinary integer subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-JUMP-001` | normative | active row | `external:DEC` | located | program preprocessing and normalized family decoder at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs#JumpSltBranchDecoder::define_decoder_subspace` |
| `ASM-JUMP-002` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner` |
| `ASM-JUMP-003` | normative | a selected source or destination register is `x0` | `external:REG` | prose | [RV32I `x0` semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); global register-memory argument | — |
| `ASM-JUMP-004` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; active current-PC lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `ASM-JUMP-005` | normative | cycle-end state | `REQ-CONT-003`; `REQ-CONT-005` | located | `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; global machine-state permutation | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:cs/src/definitions/gkr/mod.rs#MachineStatePermutationDescription` |
| `REL-JUMP-001` | normative | active `SLT`, `SLTI`, `SLTU`, or `SLTIU` row | `ASM-JUMP-001..005` | located | [RV32I comparison semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#conditional_table_resolves_signed_slti_from_immediate_sign` |
| `REL-JUMP-002` | normative | active conditional-branch row | `ASM-JUMP-001..005` | located | [RV32I conditional branches](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table` |
| `REL-JUMP-003` | normative | active `JAL` or `JALR` row | `ASM-JUMP-001..005` | located | [RV32I `JAL`/`JALR`](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table` |
