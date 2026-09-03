# Unified operations

## Imports

- `isa/unrolled/add-sub.md`
- `isa/unrolled/jump-branch-slt.md`
- `isa/unrolled/binary-shifts.md`
- `isa/unrolled/memory-word.md`

## Admitted operations

| Body | Operations |
|---|---|
| arithmetic/interface | `NOP`, `ADD`, `ADDI`, `SUB`, `LUI`, `AUIPC`, `ZimopAdd`, `ZimopSub`, `ZimopMul`, `ZimopFMA`, `ZimopTriAdd`, delegation and nondeterminism CSR operations |
| control/compare | `JAL`, `JALR`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `SLT`, `SLTI`, `SLTU`, `SLTIU` |
| bitwise/shift | `AND[I]`, `OR[I]`, `XOR[I]`, `SLL[I]`, `SRL[I]`, `SRA[I]`, `ZimopIXorRot` |
| memory | `LW`, `SW` |

## Requirements

- **`REQ-UNI-OP-001` — Shared semantics.** Operations shared with the unrolled ISA
  profile use the relations in [../unrolled/](../unrolled/).
- **`REQ-UNI-OP-002` — Tri-add.** `ZimopTriAdd` sets
  `rd <- rd_old + rs1 + rs2 mod 2^32` and requires `rd != x0`.
- **`REQ-UNI-OP-003` — Xor-rotate.** `ZimopIXorRot` sets
  `rd <- rotate_right(rs1 XOR rd_old, r)` for `r in {16,12,8,7}` and requires
  `rd != x0`.
- **`REQ-UNI-OP-004` — Reduced boundary.** Standard multiply/divide and subword
  memory operations are absent. This is an ISA-profile exclusion.
- **`REQ-UNI-OP-005` — Alignment.** Active `LW` and `SW` addresses are divisible by
  four.

## Open obligation

- **`GAP-UNI-OP-001` — Cross-profile equivalence.** Establish exhaustive equivalence
  for operations present in both unified and unrolled ISA profiles.
