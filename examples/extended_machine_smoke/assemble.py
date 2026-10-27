#!/usr/bin/env python3
"""Hand-assembled smoke program for the unified extended machine
(`cs::gkr_circuits::unified_extended_machine`): every sub-word load/store variant at every
byte offset, with and without sign extension, with negative immediates, plus MUL/MULHU on
edge operands. Run `python3 assemble.py` here to regenerate `app.bin` / `app.text` (they are
identical: no data sections). The program ends in a self-loop, which the VM treats as
termination."""
import struct

def lui(rd, imm20):
    return (imm20 & 0xfffff) << 12 | rd << 7 | 0x37

def addi(rd, rs1, imm):
    return (imm & 0xfff) << 20 | rs1 << 15 | rd << 7 | 0x13

def load(funct3, rd, rs1, imm):
    return (imm & 0xfff) << 20 | rs1 << 15 | funct3 << 12 | rd << 7 | 0x03

def store(funct3, rs2, rs1, imm):
    imm &= 0xfff
    return (imm >> 5) << 25 | rs2 << 20 | rs1 << 15 | funct3 << 12 | (imm & 0x1f) << 7 | 0x23

def rtype(funct7, funct3, rd, rs1, rs2):
    return funct7 << 25 | rs2 << 20 | rs1 << 15 | funct3 << 12 | rd << 7 | 0x33

lb, lh, lw, lbu, lhu = (lambda *a: load(0, *a)), (lambda *a: load(1, *a)), (lambda *a: load(2, *a)), (lambda *a: load(4, *a)), (lambda *a: load(5, *a))
sb, sh, sw = (lambda *a: store(0, *a)), (lambda *a: store(1, *a)), (lambda *a: store(2, *a))
mul = lambda rd, rs1, rs2: rtype(1, 0, rd, rs1, rs2)
mulhu = lambda rd, rs1, rs2: rtype(1, 3, rd, rs1, rs2)
JAL_SELF = 0x0000006f

A0, A1, A2, A3, A4, A5, A6, A7 = 10, 11, 12, 13, 14, 15, 16, 17

program = [
    lui(A0, 0x400),               # a0 = 0x0040_0000: first RAM word past the 4 MB ROM range
    lui(A1, 0x89abd),
    addi(A1, A1, -0x211),         # a1 = 0x89ab_cdef
    sw(A1, A0, 0),                # cell 0  = 0x89abcdef
    sw(A1, A0, 24),               # cell 24 = 0x89abcdef (overwritten below by sub-word stores)
    sb(A1, A0, 5),                # cell 4,  byte offset 1 := 0xef
    sh(A1, A0, 10),               # cell 8,  halfword offset 2 := 0xcdef
    sb(A1, A0, 15),               # cell 12, byte offset 3
    sh(A1, A0, 16),               # cell 16, halfword offset 0
    sb(A1, A0, 18),               # cell 16, byte offset 2
    sb(A1, A0, 20),               # cell 20, byte offset 0
    sb(A1, A0, 26),               # cell 24 (0x89abcdef), byte offset 2 := 0xef
    sh(A1, A0, 24),               # cell 24, halfword offset 0 := 0xcdef
    lb(A2, A0, 0),                # 0xef -> 0xffffffef
    lb(A2, A0, 1),                # 0xcd
    lb(A2, A0, 2),                # 0xab
    lb(A2, A0, 3),                # 0x89
    lbu(A2, A0, 0),
    lbu(A2, A0, 1),
    lbu(A2, A0, 2),
    lbu(A2, A0, 3),
    lh(A2, A0, 0),                # 0xcdef -> 0xffffcdef
    lh(A2, A0, 2),                # 0x89ab -> 0xffff89ab
    lhu(A2, A0, 0),
    lhu(A2, A0, 2),
    lh(A2, A0, 18),               # 0x00ef: positive halfword
    lb(A2, A0, 19),               # 0x00: positive byte
    lb(A2, A0, 20),               # 0xef at offset 0 of a cell that was zero
    lw(A2, A0, 4),                # partially overwritten cells read back as words
    lw(A2, A0, 16),
    lw(A2, A0, 24),
    addi(A7, A0, 8),              # a7 = a0 + 8: negative immediates (low-limb borrow)
    lb(A2, A7, -3),               # cell 4, offset 1
    lh(A2, A7, -6),               # cell 0, offset 2
    sb(A1, A7, -1),               # cell 4, offset 3
    sh(A1, A7, -8),               # cell 0, offset 0
    lhu(A2, A7, -8),
    lbu(A2, A7, -1),
    lui(A3, 0xfffff),
    addi(A3, A3, -1),             # a3 = 0xffff_ffff
    mul(A4, A3, A3),              # 1
    mulhu(A4, A3, A3),            # 0xffff_fffe
    mul(A4, A1, A3),
    mulhu(A4, A1, A3),
    mul(A4, A1, A1),
    mulhu(A4, A1, A1),
    addi(A5, 0, 0),
    mul(A4, A5, A1),              # 0
    mulhu(A4, A1, A5),            # 0
    addi(A5, 0, 1),
    mul(A4, A5, A1),              # a1
    mulhu(A4, A5, A1),            # 0
    lui(A6, 0x12345),
    addi(A6, A6, 0x678),          # a6 = 0x1234_5678
    mul(A4, A6, A1),
    mulhu(A4, A6, A1),
    mul(A4, A6, A6),
    mulhu(A4, A6, A6),
    JAL_SELF,
]

words = b"".join(struct.pack("<I", w) for w in program)
for name in ("app.bin", "app.text"):
    with open(name, "wb") as f:
        f.write(words)
print(f"{len(program)} instructions")
