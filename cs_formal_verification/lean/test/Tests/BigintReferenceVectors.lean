module
public import Human.ISA.ValidUse.Model

@[expose] public section
namespace Tests.BigintReferenceVectors
open RV.ValidUse
set_option warningAsError true

/-- Concatenation keeps the eight words in little-endian order. -/
example : bigintValue #v[0x01234567#32, 0x89abcdef#32, 0x10203040#32, 0x50607080#32,
    0x90a0b0c0#32, 0xd0e0f000#32, 0x13579bdf#32, 0x2468ace0#32] =
    0x2468ace013579bdfd0e0f00090a0b0c0506070801020304089abcdef01234567#256 := by decide +kernel

/-- Extraction restores all eight little-endian words. -/
example : bigintWords 0x2468ace013579bdfd0e0f00090a0b0c0506070801020304089abcdef01234567#256 =
    #v[0x01234567#32, 0x89abcdef#32, 0x10203040#32, 0x50607080#32,
      0x90a0b0c0#32, 0xd0e0f000#32, 0x13579bdf#32, 0x2468ace0#32] := by decide +kernel

/-- ADD propagates an incoming carry across the full width. -/
example : bigintOperation 1 true 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff#256 0 =
    some (0, true) := by decide +kernel

/-- SUB applies both the subtrahend and the incoming borrow. -/
example : bigintOperation 2 true 0 1 =
    some (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe#256, true) := by decide +kernel

/-- SUB_NEGATE subtracts the state and borrow from the message. -/
example : bigintOperation 4 true 5 11 = some (5, false) := by decide +kernel

/-- MUL_LOW returns the low half and reports overflow. -/
example : bigintOperation 8 false 0x8000000000000000000000000000000000000000000000000000000000000001#256 2 =
    some (2, true) := by decide +kernel

/-- MUL_HIGH returns bits 256 through 511 of the product. -/
example : bigintOperation 16 false 0x8000000000000000000000000000000000000000000000000000000000000003#256 4 =
    some (2, false) := by decide +kernel

/-- EQ preserves the state and reports equality. -/
example : bigintOperation 32 false 0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef#256
    0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef#256 =
    some (0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef#256, true) := by decide +kernel

/-- MEMCOPY applies the incoming carry to the message. -/
example : bigintOperation 128 true 99 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff#256 =
    some (0, true) := by decide +kernel

end Tests.BigintReferenceVectors
