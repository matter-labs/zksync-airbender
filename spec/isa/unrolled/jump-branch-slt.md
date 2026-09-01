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

Comparison instructions with `rd = x0` are rewritten to the canonical `NOP` before
this family is selected. `JAL` and `JALR` retain their control-flow effect when
`rd = x0`. Preprocessing normalizes `SLT` with `SLTI`, and `SLTU` with `SLTIU`;
source operations whose normalized operands coincide have the same family row.

## Inputs

| Name | Meaning |
|---|---|
| `pc` | current 32-bit program counter |
| `execute` | boolean cycle-activation flag |
| `rs1`, `rs2` | 32-bit values read from the selected source registers |
| `imm` | preprocessed 32-bit immediate |
| `rd` | selected destination register |
| `class` | normalized decoder class: `JAL`, `JALR`, `BRANCH`, or `COMPARE` |
| `funct3` | branch predicate or signed/unsigned comparison selector |

`imm12`, `imm13`, and `imm21` denote encoded immediate fields before preprocessing.
For jumps and branches, `imm` is their applicable two's-complement sign extension.
For comparisons, the normalized second operand is `(rs2 + imm) mod 2^32`: register
forms use `imm = 0`, while nonzero immediate forms use `rs2 = x0`. `s32(x)` interprets
the 32-bit word `x` as a signed two's-complement integer.

`x <- expression` denotes the cycle's architectural assignment to `x`. The right-hand
side uses pre-cycle values. An assignment must remain in the target's declared domain
unless the expression explicitly says `mod`. Architectural locations not assigned by
the active relation remain unchanged.

## Assumptions

- **ASM-JUMP-001 — Normalized decoder binding.** `(class, funct3, rs1_index, rs2_index, rd, imm)` is the normalized row committed for the current `pc`. Comparison rows commit signed versus unsigned comparison and the normalized second operand, but do not retain exact `SLT` versus `SLTI` or `SLTU` versus `SLTIU` source-mnemonic identity when their normalized rows coincide.
- **ASM-JUMP-002 — Activation and selector exclusivity.** Family composition gates the decoder and state contribution by `execute`. When `execute = 1`, exactly one jump, branch, or comparison class is active.
- **ASM-JUMP-003 — Register consistency.** Register reads and any destination write satisfy the global register-memory argument.
- **ASM-JUMP-004 — Zero register.** Reading `x0` returns `0`; writing `x0` preserves `0`.
- **ASM-JUMP-005 — PC alignment.** `pc mod 4 = 0` at the start of the cycle.
- **ASM-JUMP-006 — Cycle-end state closure.** The cycle-end PC participates in the global machine-state permutation and represents a 32-bit word. This imports the range/domain closure that is not locally imposed on the family circuit's final high limb.

## Canonical relation tree

> Interpret this tree under `ASM-JUMP-001..006`. The class branches within
> `execute = 1` are mutually exclusive and exhaustive.

- **`execute = 0`.** Outside this module's active-row scope.
- **`execute = 1`.**
  - **`class = COMPARE`.**
    - **[`REQ-JUMP-001`] Comparison assignment.** The normalized selector assigns `rd`, then advances `pc`:
      - **`funct3 = 0b010` (`SLT` or `SLTI`).**
        `rd <- 1` if `s32(rs1) < s32((rs2 + imm) mod 2^32)`, otherwise `rd <- 0`.
      - **`funct3 = 0b011` (`SLTU` or `SLTIU`).**
        `rd <- 1` if `rs1 < (rs2 + imm) mod 2^32` as unsigned 32-bit integers, otherwise `rd <- 0`.
      - **Both comparison selectors.**
        `pc <- (pc + 4) mod 2^32`.
  - **`class = BRANCH`.**
    - **[`REQ-JUMP-002`] Conditional branch assignment.** `branch_taken` is defined by the selected case:
      - **`funct3 = 0b000` (`BEQ`).** `branch_taken <=> rs1 = rs2`.
      - **`funct3 = 0b001` (`BNE`).** `branch_taken <=> rs1 != rs2`.
      - **`funct3 = 0b100` (`BLT`).** `branch_taken <=> s32(rs1) < s32(rs2)`.
      - **`funct3 = 0b101` (`BGE`).** `branch_taken <=> s32(rs1) >= s32(rs2)`.
      - **`funct3 = 0b110` (`BLTU`).** `branch_taken <=> rs1 < rs2` as unsigned 32-bit integers.
      - **`funct3 = 0b111` (`BGEU`).** `branch_taken <=> rs1 >= rs2` as unsigned 32-bit integers.
      - **`branch_taken = 0`.**
        `pc <- (pc + 4) mod 2^32`.
      - **`branch_taken = 1`.**
        `((pc + imm) mod 2^32) mod 4 = 0`;
        `pc <- (pc + imm) mod 2^32`.
  - **`class = JAL` or `class = JALR`.**
    - **[`REQ-JUMP-003`] Jump assignment.** First assign the link value:
      - **`rd != x0`.**
        `rd <- (pc + 4) mod 2^32`.
      - **`rd = x0`.**
        `x0 <- 0`.
      - **`class = JAL`.**
        `((pc + imm) mod 2^32) mod 4 = 0`;
        `pc <- (pc + imm) mod 2^32`.
      - **`class = JALR`.**
        `(((rs1 + imm) mod 2^32) & 0xfffffffe) mod 4 = 0`;
        `pc <- ((rs1 + imm) mod 2^32) & 0xfffffffe`.

## Derived facts

For a quick structural view of every active row:

- comparison results are always `0` or `1` by `REQ-JUMP-001`;
- every assigned `pc` is a 32-bit word divisible by four by `ASM-JUMP-005..006`
  and `REQ-JUMP-001..003`;
- JALR clears target bit zero, and its four-byte alignment predicate also requires
  target bit one to be zero, by `REQ-JUMP-003`;
- PC-target and link additions wrap modulo `2^32`; this family does not enforce a
  non-wrapping upper bound analogous to ADD's `pc + 4 < 2^32`;
- only a comparison or jump destination can change among the registers; branch rows
  leave all architectural registers unchanged, and `x0` remains zero by
  `ASM-JUMP-004`.

## Implementation conformance

At `dfb1b2a8a`, the not-taken-branch witness default in
`apply_jump_branch_slt_inner` assigns the final-overflow and low-limb-carry witnesses
in the opposite order. For example, `pc = 0x0000fffc` needs low carry `1` and final
overflow `0`, but the default witness supplies `0` and `1`, so witness generation can
fail the low-limb equation for the valid transition in `REQ-JUMP-002`. This is a
prover-completeness implementation defect; it does not change the specified relation.

## Metadata

These relations are normative for the stated unrolled profile. Ordinary instruction
semantics adopt the official [RV32I Base Integer Instruction Set, Version 2.1](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html),
with Airbender-specific alignment and wrapping behavior supported by project decisions
and convergent implementation evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled `jump_branch_slt_family`, ordinary integer subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-JUMP-001` | normative | active row | `external:DEC` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs#JumpSltBranchDecoder::define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs#JumpSltBranchDecoder::define_decoder_subspace` |
| `ASM-JUMP-002` | normative | active row | `external:DEC`; `external:MACH` | located | admitted selector rows in `repo:cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs#JumpSltBranchDecoder::define_decoder_subspace@dfb1b2a8a`; execute-gated decoder lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs#JumpSltBranchDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `ASM-JUMP-003` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner` |
| `ASM-JUMP-004` | normative | `rs_index = 0 || rd = 0` | `external:REG` | prose | RV32I `x0` semantics; global register-memory argument | — |
| `ASM-JUMP-005` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; active current-PC lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `ASM-JUMP-006` | normative | cycle-end state | `external:MACH` | located | `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a`; `repo:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation@dfb1b2a8a`; global machine-state permutation | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:cs/src/definitions/gkr/mod.rs#MachineStatePermutationDescription` |
| `REQ-JUMP-001` | normative | active comparison row | `ASM-JUMP-001..006` | located | RV32I comparisons; `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#conditional_table_resolves_signed_slti_from_immediate_sign` |
| `REQ-JUMP-002` | normative | active branch row | `ASM-JUMP-001..006` | located | RV32I conditional branches; `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_conditional_op_resolution_table`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table` |
| `REQ-JUMP-003` | normative | active jump row | `ASM-JUMP-001..006` | located | RV32I `JAL`/`JALR`; `repo:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner@dfb1b2a8a`; `repo:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs#apply_jump_branch_slt_inner`; `symbol:cs/src/tables/jump_branch_opcode_related.rs#create_jump_cleanup_offset_table` |
