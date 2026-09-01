# ADD: Integer add/subtract family

## Supported operations

- `ADD rd, rs1, rs2`
- `ADDI rd, rs1, imm12`
- `LUI rd, imm20`
- `SUB rd, rs1, rs2`
- `AUIPC rd, imm20`

Any listed instruction with `rd = x0` is represented by the canonical `NOP` row.

## Inputs

| Name | Meaning |
|---|---|
| `pc` | current 32-bit program counter |
| `execute` | boolean cycle-activation flag |
| `rs1`, `rs2` | 32-bit values read from the selected source registers |
| `imm` | preprocessed 32-bit immediate |
| `rd` | selected destination register |
| `op` | one of `ADD`, `ADDI`, `LUI`, `SUB`, `AUIPC`, or `NOP` |

`imm12` and `imm20` denote the encoded immediate fields before preprocessing. Machine
words are 32-bit values; source-value consistency follows from `ASM-ADD-003`.

`x <- expression` denotes the cycle's architectural assignment to `x`. The right-hand
side uses pre-cycle values. An assignment must remain in the target's declared domain
unless the expression explicitly says `mod`. Architectural locations not assigned by
the active relation remain unchanged.

## Assumptions

- **ASM-ADD-001 — Decoder binding.** `(op, rs1_index, rs2_index, rd, imm)` is the row committed for the current `pc`.
- **ASM-ADD-002 — Selector exclusivity.** Exactly one full-family operation selector is active.
- **ASM-ADD-003 — Register consistency.** Register reads and the destination write satisfy the global register-memory argument.
- **ASM-ADD-004 — Zero register.** Reading `x0` returns `0`; writing `x0` preserves `0`.
- **ASM-ADD-005 — PC alignment.** `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-ADD-001..005`. Within `execute = 1`, the numbered
> requirements are conjoined. The cases below `REQ-ADD-001` are mutually
> exclusive.

- **`execute = 0`.** Outside this module's active-row scope.
- **`execute = 1`.**
  - **[`REQ-ADD-001`] Destination assignment.** The selected case assigns `rd`:
    - **`op = ADD`.**
      `rd <- (rs1 + rs2) mod 2^32`.
    - **`op = ADDI`.**
      `rd <- (rs1 + sign_extend_12(imm12)) mod 2^32`.
    - **`op = LUI`.**
      `rd <- imm20 << 12`.
    - **`op = SUB`.**
      `rd <- (rs1 - rs2) mod 2^32`.
    - **`op = AUIPC`.**
      `rd <- (pc + (imm20 << 12)) mod 2^32`.
    - **`op = NOP` or a listed instruction has `rd = x0`.**
      `rd <- 0`.
  - **[`REQ-ADD-002`] Non-wrapping PC assignment.**
    `pc + 4 < 2^32`;
    `pc <- pc + 4`.

## Derived facts

For a quick structural view of every active row:

- arithmetic overflow and subtraction underflow wrap rather than reject by
  `REQ-ADD-001` and the register word domain;
- `ASM-ADD-005` and `REQ-ADD-002` imply `pc <= 2^32 - 8` before the
  assignment and `pc <= 2^32 - 4` afterward;
- `ASM-ADD-005` and `REQ-ADD-002` imply that the assigned `pc` remains divisible
  by four;
- among registers, at most `rd` changes by `REQ-ADD-001` and the assignment
  convention; `x0` remains zero by `ASM-ADD-004`.

## Metadata

These relations are normative for the stated unrolled profile. Ordinary instruction
semantics adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html);
Airbender-specific boundaries are supported by project decisions and convergent
constraint and architecture evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled `add_sub_lui_auipc_mop`, ordinary integer subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-ADD-001` | normative | active row | `external:DEC` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace` |
| `ASM-ADD-002` | normative | active row | `external:DEC` | located | `repo:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace` |
| `ASM-ADD-003` | normative | active row | `external:REG` | located | `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `ASM-ADD-004` | normative | `rs_index = 0 || rd = 0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-ADD-005` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; active current-PC lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REQ-ADD-001` | normative | active operation row | `ASM-ADD-001..004` | located | `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `REQ-ADD-002` | normative | active row | 32-bit `pc` input domain | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
