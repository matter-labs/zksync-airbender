## ADD/SUB/LUI/MOP family

- 1 bit for each `ADD/ADDI/SUB/LUI/ADDMOD/SUBMOD/MULMOD`

Total of 7 bits

## JAL/JALR/BRANCH/SLT(U)/AUIPC family

The only family that modifies PC

- 1 bits to indicate `I` variant for `SLTI/SLTIU/SLT/SLTU`
- `SLT/BRANCH` differentiate by `funct3`
- 4 bits for `JAL/JALR/SLT(U) + BRANCH/AUIPC` famity

Total of 5 bits

## SHIFT/BINOPS/CSRRW (no CSRRWI variant) family

- 1 bit for `I` variant for shifts or binops
- binops differentiate by `funct3`
- 1 bit for each `SLL/SRL/SRA/BINOP/CSRRW`

Total of 6 bits

## MUL/DIV family

Technically we could differentiate by `funct3`, but it would lead to more variables

- 1 bit to differentiate MUL/DIV
- 3 bits for either `MUL/MULH/MULHSU` or `DIVU/DIV/REM` (`MULHU` and `REMU` are just negations of `MUL/DIVU`)

Total of 4 bits

## Memory ops family

- 1 bit to differentiate LOAD/STORE
- 1 bit to indicate sign extension for LOADs
- 3 bits for full word/half word/byte for both loads and stores

Total of 5 bits

## Generic structure of the decoder table

Decoder table takes a combination of `opcode` (7 bits) + `funct3` (3 bits) + `funct7` (7 bits) pieces as the input, and outputs 2 values:
- opcode family. It's a variable that will participate directly in the permutation argument over states
- linear combination of bitmask of `invalid || opcode_format_bits` to select immediate - this part will be bit-decomposed by the decoder for it's work - and 8 bit coarsely constrained bitmask that will be a variable named `circuit_family_extra_mask` in the permutation argument over states 
