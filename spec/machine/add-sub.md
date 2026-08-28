# ADD: Integer add/subtract family

> Draft prototype. Covers `ADD`, `ADDI`, `LUI`, `SUB`, and `AUIPC` in the
> unrolled `add_sub_lui_auipc_mop` circuit. MOP, delegation, and
> nondeterminism operations are out of scope.

## What this component guarantees

For one active cycle, the component:

1. reads the decoder-selected registers;
2. writes the operation result to the decoder-selected destination;
3. advances `pc` by four without wrapping past `2^32 - 1`.

Arithmetic results wrap modulo `2^32`. Program-counter overflow is rejected.

## Inputs

| Name | Meaning |
|---|---|
| `pc` | current 32-bit program counter |
| `execute` | boolean cycle-activation flag |
| `rs1`, `rs2` | 32-bit values read from the selected source registers |
| `imm` | preprocessed 32-bit immediate |
| `rd` | selected destination register |
| `op` | one of `ADD`, `ADDI`, `LUI`, `SUB`, `AUIPC`, or `NOP` |

Each 32-bit value is represented by two 16-bit limbs. Destination limbs are
range-checked locally; source-value range follows from `ASM-ADD-003`.

## Assumptions

- **ASM-ADD-001 — Decoder binding.** `(op, rs1_index, rs2_index, rd, imm)` is the row committed for the current `pc`.
- **ASM-ADD-002 — Selector exclusivity.** Exactly one full-family operation selector is active.
- **ASM-ADD-003 — Register consistency.** Register reads and the destination write satisfy the global register-memory argument.
- **ASM-ADD-004 — Zero register.** Reading `x0` returns `0`; writing `x0` preserves `0`.

## Decision tree

> Under `ASM-ADD-001..004`. Experimental navigation view; leaf IDs name canonical
> statements.

- **`execute = 0`.** Outside this module's active-row scope.
- **`execute = 1`.**
  - **`pc > 2^32 - 5`.** No satisfying row. `REJ-ADD-001`.
  - **`pc <= 2^32 - 5`.** The decoded `op` selects one row of the operation table.
    - **Destination differs from the selected result.** No satisfying row.
      `REJ-ADD-002`.
    - **Destination equals the selected result.** Enforce the destination value and
      range (`REQ-ADD-001`, `REQ-ADD-002`), advance `pc` (`REQ-ADD-003`), apply the
      register effect (`REQ-ADD-004`), and export the next state (`OUT-ADD-001`).

The operation table below partitions the decoded `op` branch.

## Operation relation

The preprocessor maps source instructions into the following canonical rows:

| Source instruction | Canonical operands | Required destination value |
|---|---|---|
| `ADD rd, rs1, rs2` | `imm = 0` | `rs1 + rs2 mod 2^32` |
| `ADDI rd, rs1, imm` | `rs2 = x0`; `imm = sign_extend_12(imm)` | `rs1 + imm mod 2^32` |
| `LUI rd, imm` | `rs1 = x0`; `rs2 = x0`; `imm = imm20 << 12` | `imm` |
| `SUB rd, rs1, rs2` | `imm = 0` | `rs1 - rs2 mod 2^32` |
| `AUIPC rd, imm` | `rs1 = x0`; `rs2 = x0`; `imm = imm20 << 12` | `pc + imm mod 2^32` |
| `NOP` or a listed instruction with `rd = x0` | `rs1 = x0`; `rs2 = x0`; `rd = x0`; `imm = 0` | `0` |

### REQ-ADD-001 — Destination value

For an active row, the destination write equals the value in the table above.
Result overflow and subtraction underflow wrap modulo `2^32`.

### REQ-ADD-002 — Output range

The low and high limbs of the destination write are each in `[0, 2^16)`.

### REQ-ADD-003 — Sequential program counter

`pc_next = pc + 4` as an integer, with `pc + 4 < 2^32`.

### REQ-ADD-004 — Register-state effect

The cycle emits two register reads and one destination read/write. Under
`ASM-ADD-003`, the only changed architectural register is `rd`, with the value
required by `REQ-ADD-001`; `x0` remains zero.

## Preserved invariants

- **INV-ADD-001 — Word range.** Every destination value remains in `[0, 2^32)`.
- **INV-ADD-002 — PC alignment.** `pc mod 4 = 0 => pc_next mod 4 = 0`.
- **INV-ADD-003 — Zero register.** `Reg[x0] = 0 => Reg_next[x0] = 0`.

## Rejections

- **REJ-ADD-001 — PC overflow.** `pc > 2^32 - 5` admits no row satisfying `REQ-ADD-003`.
- **REJ-ADD-002 — Wrong result.** A destination value differing from the selected table equation admits no row satisfying `REQ-ADD-001`.

## Output

- **OUT-ADD-001.** `(Reg_next, pc_next)` satisfies `REQ-ADD-001..004` under `ASM-ADD-001..004`.

## Open boundary

- **GAP-ADD-001.** This prototype covers the unrolled family implementation only. Confirm that the unified implementation must expose the identical ordinary-integer relation, then pin both implementations to this module.

## Metadata

All claims are recovered from implementation evidence and remain `provisional` until
confirmed as project decisions. Evidence was checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled `add_sub_lui_auipc_mop`, ordinary integer subrelation

### Semantic metadata

| ID | Authority | Activation | Depends / discharged by |
|---|---|---|---|
| `ASM-ADD-001` | provisional | active row | `external:DEC` |
| `ASM-ADD-002` | provisional | active row | `external:DEC` |
| `ASM-ADD-003` | provisional | active row | `external:REG` |
| `ASM-ADD-004` | provisional | `rs_index = 0 || rd = 0` | `external:REG` |
| `REQ-ADD-001` | provisional | active ordinary operation | `ASM-ADD-001..004` |
| `REQ-ADD-002` | provisional | active row | — |
| `REQ-ADD-003` | provisional | active row | `ASM-ADD-001` |
| `REQ-ADD-004` | provisional | active row | `ASM-ADD-003`, `ASM-ADD-004`, `REQ-ADD-001` |
| `INV-ADD-001` | provisional | destination write | `REQ-ADD-002` |
| `INV-ADD-002` | provisional | active row | `REQ-ADD-003` |
| `INV-ADD-003` | provisional | active row | `ASM-ADD-004`, `REQ-ADD-004` |
| `REJ-ADD-001` | provisional | active row | `REQ-ADD-003` |
| `REJ-ADD-002` | provisional | active ordinary operation | `REQ-ADD-001` |
| `OUT-ADD-001` | provisional | active row | `REQ-ADD-001..004` |
| `GAP-ADD-001` | open | — | affects `OUT-ADD-001`; owner `human` |

### Implementation trace metadata

| ID | Binding | Source | Anchor / check |
|---|---|---|---|
| `ASM-ADD-001` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace` |
| `ASM-ADD-002` | located | `repo:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#define_decoder_subspace` |
| `ASM-ADD-003` | located | `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a`; global register-memory argument | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `ASM-ADD-004` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `REQ-ADD-001` | located | `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `REQ-ADD-002` | located | direct destination-limb range checks in `apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `REQ-ADD-003` | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
| `REQ-ADD-004` | located | register requests in `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `INV-ADD-001` | prose | `derived:REQ-ADD-002` | — |
| `INV-ADD-002` | prose | `derived:REQ-ADD-003` | — |
| `INV-ADD-003` | prose | `derived:ASM-ADD-004+REQ-ADD-004` | — |
| `REJ-ADD-001` | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
| `REJ-ADD-002` | located | selected arithmetic constraint in `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner` |
| `OUT-ADD-001` | prose | `derived:REQ-ADD-001..004` | — |
| `GAP-ADD-001` | — | unrolled implementation inspected; unified relation not yet pinned | — |
