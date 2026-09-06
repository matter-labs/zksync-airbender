# Normative RV32 Machine Baseline

Use this reference only when repository evidence shows that the target circuit implements a RISC-V machine. It is vendor-neutral and intentionally contains no Airbender, Boojum, branch, or proving-profile claims.

## Normative references

- [RV32I Base Integer Instruction Set, Version 2.1](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html), official versioned and text-searchable HTML.
- [M Extension for Integer Multiplication and Division, Version 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html), only if the target profile claims M operations.
- [Zicsr Extension, Version 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html), only if the target claims architectural CSR instructions.
- [Zimop Extension, Version 1.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/zimop.html), for standard encoding and compatibility semantics. A project may deliberately assign custom semantics to selected encodings; those semantics must come from a versioned project profile.

Prefer these pages over a simulator or circuit implementation when establishing ordinary RISC-V semantics.

## RV32I contract

The base architectural state has 32 general-purpose 32-bit registers `x0..x31`, a 32-bit program counter, and `XLEN = 32`. `x0` always reads as zero and discards writes. Ordinary arithmetic wraps modulo `2^32`; signed operations use two's-complement interpretation and unsigned operations use the same bits as `u32`.

The ordinary RV32I groups are:

- upper/immediate/arithmetic: `LUI`, `AUIPC`, `ADDI`, `ADD`, `SUB`;
- comparisons: `SLTI`, `SLTIU`, `SLT`, `SLTU`;
- Boolean and shifts: `XORI`, `ORI`, `ANDI`, `SLLI`, `SRLI`, `SRAI`, `XOR`, `OR`, `AND`, `SLL`, `SRL`, `SRA`;
- control flow: `JAL`, `JALR`, `BEQ`, `BNE`, `BLT`, `BLTU`, `BGE`, `BGEU`;
- memory: `LB`, `LBU`, `LH`, `LHU`, `LW`, `SB`, `SH`, `SW`;
- ordering/system encodings described separately by the unprivileged specification.

Apply the specification's exact edge semantics, including:

- I/S/B/J immediates are sign-extended; U-immediates occupy the high 20 bits;
- register shifts use `rs2[4:0]`; immediate shifts use their encoded five-bit amount;
- `JAL` writes old `pc + 4` and jumps to old `pc + signext(offset)`;
- `JALR` writes old `pc + 4` and jumps to `(rs1 + signext(imm)) & ~1`;
- a taken branch uses old `pc + signext(offset)` and an untaken branch uses old `pc + 4`;
- loads sign- or zero-extend exactly as named, and subword stores replace only selected bytes;
- writing `rd = x0` discards the result but does not suppress architectural side effects or exceptions;
- supported instruction alignment, data alignment, endianness, and exception behavior are determined by the applicable ISA and execution-environment specifications, not by RV32I mnemonic names alone.

## Optional M contract

Do not infer M support from dormant enums or circuits. If the selected machine profile enables an M operation, apply the official M semantics, including:

- the signedness of `MULH`, `MULHSU`, and `MULHU`;
- division by zero and the corresponding remainder result;
- signed `MIN / -1` overflow and its remainder;
- the distinction between `DIV`/`REM` and `DIVU`/`REMU`.

## Required project delta

Before auditing, pair this baseline with an applicable, versioned project profile or recover an explicit delta. At minimum resolve:

- exact repository/release/commit and active proving entrypoint;
- ISA subsets and profiles, including compressed, M, privileged, system, CSR, and custom operations;
- unsupported-encoding behavior: preprocessing rejection, illegal row, trap, or merely unprovable execution;
- any preprocessing rewrite, especially `rd = x0` handling;
- endianness, alignment, address width, RAM/ROM regions, and initialization;
- custom instruction encodings, operand mapping, arithmetic domain, and field representation;
- initial state, public inputs/outputs, success condition, final state, and termination;
- differences between preprocessing, simulator/replayer, constraint circuits, and verifier statement.

If no applicable versioned profile exists, these are specification questions until established from authoritative repository evidence. Never transfer a project delta across a different proof system merely because both repositories contain algebraic circuits.
