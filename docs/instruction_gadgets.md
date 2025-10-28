# Instruction gadgets and delegated opcode families

This document explains, from a RISC‑V perspective, which opcode families are implemented directly inside the main machine circuit (as “instruction gadgets”) and which families are implemented as separate circuits and invoked via delegation.

## What lives in the main machine (native gadgets)

These opcode families are proven by the main RISC‑V machine. You write standard RV32I/M code; the circuit enforces their semantics natively.

- Arithmetic and bitwise: `ADD`/`ADDI`, `SUB`, `AND`/`ANDI`, `OR`/`ORI`, `XOR`/`XORI`.
- Shifts: `SLL`/`SLLI`, `SRL`/`SRLI`, `SRA`/`SRAI` (shift amounts masked to 5 bits).
- Multiply/Divide (RV32M): `MUL`, `MULH`, `MULHSU`, `MULHU`, `DIV`, `DIVU`, `REM`, `REMU`.
  - Some configurations exclude signed MUL/DIV/REM to shrink proofs (see Machine Configuration doc).
- Loads/Stores: `LB`/`LBU`, `LH`/`LHU`, `LW`, `SB`, `SH`, `SW`.
  - Minimal configurations keep only word-aligned `LW`/`SW` to stay small.
- Branching and jumps: `BEQ`, `BNE`, `BLT`/`BLTU`, `BGE`/`BGEU`, `JAL`, `JALR`.
- Upper immediates and PC-relative: `LUI`, `AUIPC`.
- CSR data‑movement: `CSRRW`, `CSRRS`, `CSRRC` (and immediates).
  - Whether non‑delegation CSRs are allowed depends on the chosen machine configuration.

For details on exact support per machine variant, see `docs/machine_configuration.md`.

## Families implemented by separate circuits (delegations)

Heavy families that are expensive to encode per instruction are implemented as standalone circuits and are invoked via a single custom CSR. Write to CSR `0x7C0` with a per‑circuit `DELEGATION_TYPE_ID` and pass inputs/outputs via registers and memory pointers defined by the circuit’s ABI. From the RISC‑V perspective, this behaves like a single instruction that consumes inputs and writes back results; the circuit enforces the same memory/register effects inside the unified memory argument.

Supported delegation circuits today:

- BLAKE2 with compression
  - Purpose: fast hashing for Merkle commitments, transcripts, random oracles.
  - RISC‑V view: provide pointers to state and message blocks; circuit returns the compressed state.
- BigInt with control (u256 arithmetic)
  - Purpose: 256‑bit arithmetic used across BN254 field ops and as building blocks for secp256k1, secp256r1, BLS12‑family curves, and modular exponentiation.
  - RISC‑V view: pass pointers to u256 operands and a control mask selecting the operation (e.g., ADD/SUB/MUL_LOW/MUL_HIGH/EQ/CARRY/MEMCOPY); circuit writes results back via the provided pointers.

See `docs/delegation_circuits.md` for ABIs, control masks, and register conventions used by each delegation circuit.

Note: using a custom CSR opcode to call precompiles allows us to significantly optimize expensive algorithms (hashing, wide‑word arithmetic) by proving them in compact dedicated circuits instead of expanding them into many primitive machine steps.

### Opcode semantics at a glance

`Arithmetic and bitwise`: add/sub compute 32‑bit sums/differences (with wraparound as per RV32); AND/OR/XOR apply the corresponding bitwise operation.

`Shifts`: SLL shifts left; SRL shifts right logically (zero fill); SRA shifts right arithmetically (sign‑extend). Shift amounts use only the low 5 bits.

`Multiply/Divide`: MUL returns the low 32 bits of the product; MULH/MULHSU/MULHU return the high 32 bits with various signedness; DIV/DIVU produce quotient; REM/REMU produce remainder following the RISC‑V spec edge‑case rules.

`Loads/Stores`: LB/LBU, LH/LHU, LW load 8/16/32 bits (with optional sign extension for LB/LH); SB/SH/SW store 8/16/32 bits. Minimal machines restrict to aligned 32‑bit LW/SW only.

`Branches and jumps`: BEQ/BNE/BLT/… conditionally set PC to PC+imm; JAL writes return address (PC+4) to rd and jumps to PC+imm; JALR writes PC+4 to rd and jumps to rs1+imm with bit 0 cleared.

`Upper immediates`: LUI writes imm<<12 to rd; AUIPC writes PC+imm<<12 to rd.

`CSRs (data movement)`: CSRRW swaps rd with the CSR value; CSRRS sets bits; CSRRC clears bits (immediate forms use a 5‑bit uimm in place of rs1).

`Delegation CSR`: write `DELEGATION_TYPE_ID` through CSR `0x7C0` and provide inputs/outputs via the circuit‑specific ABI; the precompile performs the heavy operation and writes back results.


For a concrete view of instruction behavior in software, see our RISC‑V simulator in `risc_v_simulator/` (start with `risc_v_simulator/README.md`). The simulator shows how the ISA is executed step‑by‑step before being proven by the circuits.
