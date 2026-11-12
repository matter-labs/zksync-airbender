module
public import Human.Circuits.Blake2G.Tables.Controller
public import Human.Helpers.Core.Word
public import Slop.NonVacuous.HonestAttr
public import Mathlib.Data.ZMod.Defs
public import Human.Helpers.Context.Timestamps
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-! The honest assignment of one Blake2s G row (`Blake2G.importedConstraints`' columns, numbered as the
    artifact numbers them): computed from the row's inputs, the read words, the previous write clocks of its nine
    ports and its invocation clock. Every intermediate column is the honest value of the imported equations: the
    carries of the four additions, the byte/chunk splits and XORs of the four rotations, and the controller row at
    the read control word. -/

namespace Airbender.NonVacuous.Blake2GSpan
open Arithmetic

/-- The inputs of one G row: the control word read from x12 (low limb), the two pointers, the four state and two
    message words read, the previous (low) clock of each port (in port order) and the invocation clock. -/
structure RowInput where
  control : Nat
  statePointer : Word
  messagePointer : Word
  a : Word
  b : Word
  c : Word
  d : Word
  mx : Word
  my : Word
  previous : Fin 9 → Nat
  invocation : Nat

namespace RowInput
variable (x : RowInput)

/-- The controller row selected by the active row's control word: next control, four lanes, two message words. -/
def controls : Vector Nat 7 := Blake2G.Control.controllerRows ⟨256 + x.control % 256, by omega⟩

/-- First addition `a + b + mx`: low sum and carry, high sum and carry. -/
def sumA0 : Nat := x.a.lo + x.b.lo + x.mx.lo
def carryA0 : Nat := x.sumA0 / 65536
def a1lo : Nat := x.sumA0 % 65536
def sumA1 : Nat := x.a.hi + x.b.hi + x.mx.hi + x.carryA0
def carryA1 : Nat := x.sumA1 / 65536
def a1hi : Nat := x.sumA1 % 65536

/-- `d ^ a1` byte-wise, then rotated by 16. -/
def xd0 : Nat := (x.d.lo % 256) ^^^ (x.a1lo % 256)
def xd1 : Nat := (x.d.lo / 256) ^^^ (x.a1lo / 256)
def xd2 : Nat := (x.d.hi % 256) ^^^ (x.a1hi % 256)
def xd3 : Nat := (x.d.hi / 256) ^^^ (x.a1hi / 256)
def d1lo : Nat := x.xd2 + 256 * x.xd3
def d1hi : Nat := x.xd0 + 256 * x.xd1

/-- `c + d1`. -/
def sumC0 : Nat := x.c.lo + x.d1lo
def carryC0 : Nat := x.sumC0 / 65536
def c1lo : Nat := x.sumC0 % 65536
def sumC1 : Nat := x.c.hi + x.d1hi + x.carryC0
def carryC1 : Nat := x.sumC1 / 65536
def c1hi : Nat := x.sumC1 % 65536

/-- `b ^ c1` in 3/9/4-bit chunks per limb, then rotated by 12. -/
def xb0 : Nat := (x.b.lo % 8) ^^^ (x.c1lo % 8)
def xb1 : Nat := (x.b.lo / 8 % 512) ^^^ (x.c1lo / 8 % 512)
def xb2 : Nat := (x.b.lo / 4096) ^^^ (x.c1lo / 4096)
def xb3 : Nat := (x.b.hi % 8) ^^^ (x.c1hi % 8)
def xb4 : Nat := (x.b.hi / 8 % 512) ^^^ (x.c1hi / 8 % 512)
def xb5 : Nat := (x.b.hi / 4096) ^^^ (x.c1hi / 4096)
def b1lo : Nat := x.xb2 + 16 * x.xb3 + 128 * x.xb4
def b1hi : Nat := x.xb5 + 16 * x.xb0 + 128 * x.xb1

/-- Second addition `a1 + b1 + my`. -/
def sumA2 : Nat := x.a1lo + x.b1lo + x.my.lo
def carryA2 : Nat := x.sumA2 / 65536
def a2lo : Nat := x.sumA2 % 65536
def sumA3 : Nat := x.a1hi + x.b1hi + x.my.hi + x.carryA2
def carryA3 : Nat := x.sumA3 / 65536
def a2hi : Nat := x.sumA3 % 65536

/-- `d1 ^ a2` byte-wise, then rotated by 8. -/
def xe0 : Nat := x.xd2 ^^^ (x.a2lo % 256)
def xe1 : Nat := x.xd3 ^^^ (x.a2lo / 256)
def xe2 : Nat := x.xd0 ^^^ (x.a2hi % 256)
def xe3 : Nat := x.xd1 ^^^ (x.a2hi / 256)
def d2lo : Nat := x.xe1 + 256 * x.xe2
def d2hi : Nat := x.xe3 + 256 * x.xe0

/-- `c1 + d2`. -/
def sumC2 : Nat := x.c1lo + x.d2lo
def carryC2 : Nat := x.sumC2 / 65536
def c2lo : Nat := x.sumC2 % 65536
def sumC3 : Nat := x.c1hi + x.d2hi + x.carryC2
def carryC3 : Nat := x.sumC3 / 65536
def c2hi : Nat := x.sumC3 % 65536

/-- `b1 ^ c2` in 7/9-bit chunks per limb, then rotated by 7. -/
def xf0 : Nat := (x.xb2 + 16 * x.xb3) ^^^ (x.c2lo % 128)
def xf1 : Nat := x.xb4 ^^^ (x.c2lo / 128)
def xf2 : Nat := (16 * x.xb0 + x.xb5) ^^^ (x.c2hi % 128)
def xf3 : Nat := x.xb1 ^^^ (x.c2hi / 128)

/-- The written words. -/
def b2lo : Nat := x.xf1 + 512 * x.xf2
def b2hi : Nat := x.xf3 + 512 * x.xf0

/-- The honest value of every column. -/
def column : Nat → Nat
  | 0 => 1
  | 1 => x.invocation
  | 2 => 0
  | 3 => x.control
  | 4 => 0
  | 5 => x.controls[0]
  | 6 => 0
  | 7 => x.controls[1]
  | 8 => x.controls[2]
  | 9 => x.controls[3]
  | 10 => x.controls[4]
  | 11 => x.controls[5]
  | 12 => x.controls[6]
  | 13 => x.statePointer.lo
  | 14 => x.statePointer.hi
  | 15 => x.a.lo
  | 16 => x.a.hi
  | 17 => x.a2lo
  | 18 => x.a2hi
  | 19 => x.b.lo
  | 20 => x.b.hi
  | 21 => x.b2lo
  | 22 => x.b2hi
  | 23 => x.c.lo
  | 24 => x.c.hi
  | 25 => x.c2lo
  | 26 => x.c2hi
  | 27 => x.d.lo
  | 28 => x.d.hi
  | 29 => x.d2lo
  | 30 => x.d2hi
  | 31 => x.messagePointer.lo
  | 32 => x.messagePointer.hi
  | 33 => x.mx.lo
  | 34 => x.mx.hi
  | 35 => x.my.lo
  | 36 => x.my.hi
  | 37 => x.carryA0 % 2
  | 38 => x.carryA0 / 2
  | 39 => x.carryA1 % 2
  | 40 => x.carryA1 / 2
  | 41 => x.a1lo % 256
  | 42 => x.a1hi % 256
  | 43 => x.d.lo % 256
  | 44 => x.xd0
  | 45 => x.xd1
  | 46 => x.d.hi % 256
  | 47 => x.xd2
  | 48 => x.xd3
  | 49 => x.carryC0
  | 50 => x.carryC1
  | 51 => x.c1lo % 8
  | 52 => x.c1lo / 8 % 512
  | 53 => x.c1hi % 8
  | 54 => x.c1hi / 8 % 512
  | 55 => x.b.lo % 8
  | 56 => x.b.lo / 8 % 512
  | 57 => x.xb0
  | 58 => x.xb1
  | 59 => x.xb2
  | 60 => x.b.hi % 8
  | 61 => x.b.hi / 8 % 512
  | 62 => x.xb3
  | 63 => x.xb4
  | 64 => x.xb5
  | 65 => x.carryA2 % 2
  | 66 => x.carryA2 / 2
  | 67 => x.carryA3 % 2
  | 68 => x.carryA3 / 2
  | 69 => x.a2lo % 256
  | 70 => x.a2hi % 256
  | 71 => x.xe0
  | 72 => x.xe1
  | 73 => x.xe2
  | 74 => x.xe3
  | 75 => x.carryC2
  | 76 => x.carryC3
  | 77 => x.c2lo % 128
  | 78 => x.c2hi % 128
  | 79 => x.xf0
  | 80 => x.xf1
  | 81 => x.xf2
  | 82 => x.xf3
  | n => if h : 83 ≤ n ∧ n < 110 then
      (if (n - 83) % 3 = 0 then x.previous ⟨(n - 83) / 3, by omega⟩ else if (n - 83) % 3 = 1 then 0 else 1)
    else 0

/-- The ranges the honest row needs: an eight-bit control word, 64-aligned pointers, canonical words, previous
    clocks below the write clock, and an invocation clock that is 1 mod 4 with room for the writes. -/
structure Valid (x : RowInput) : Prop where
  control : x.control < 256
  statePointer : x.statePointer.Bounded ∧ x.statePointer.lo % 64 = 0
  messagePointer : x.messagePointer.Bounded ∧ x.messagePointer.lo % 64 = 0
  a : x.a.Bounded
  b : x.b.Bounded
  c : x.c.Bounded
  d : x.d.Bounded
  mx : x.mx.Bounded
  my : x.my.Bounded
  previous : ∀ j, x.previous j < x.invocation + 2
  invocation : x.invocation % 4 = 1
  room : x.invocation + 2 < Trace.timestampBase

/-- The chunk widths of every XOR. -/
theorem Valid.xors {x : RowInput} (valid : x.Valid) :
    x.xd0 < 256 ∧ x.xd1 < 256 ∧ x.xd2 < 256 ∧ x.xd3 < 256 ∧ x.xb0 < 8 ∧ x.xb1 < 512 ∧ x.xb2 < 16 ∧ x.xb3 < 8 ∧
      x.xb4 < 512 ∧ x.xb5 < 16 ∧ x.xe0 < 256 ∧ x.xe1 < 256 ∧ x.xe2 < 256 ∧ x.xe3 < 256 ∧ x.xf0 < 128 ∧
      x.xf1 < 512 ∧ x.xf2 < 128 ∧ x.xf3 < 512 := by
  have b := valid.b
  have d := valid.d
  simp only [Word.Bounded, limbBase] at b d
  have byte {m n : Nat} (hm : m < 256) (hn : n < 256) : m ^^^ n < 256 := Nat.xor_lt_two_pow (n := 8) hm hn
  have chunk {k m n : Nat} (hm : m < 2 ^ k) (hn : n < 2 ^ k) : m ^^^ n < 2 ^ k := Nat.xor_lt_two_pow hm hn
  have xd0 : x.xd0 < 256 := byte (by omega) (by omega)
  have xd1 : x.xd1 < 256 := byte (by omega) (by simp only [a1lo]; omega)
  have xd2 : x.xd2 < 256 := byte (by omega) (by omega)
  have xd3 : x.xd3 < 256 := byte (by omega) (by simp only [a1hi]; omega)
  have xb0 : x.xb0 < 8 := chunk (k := 3) (by omega) (by omega)
  have xb1 : x.xb1 < 512 := chunk (k := 9) (by omega) (by omega)
  have xb2 : x.xb2 < 16 := chunk (k := 4) (by omega) (by simp only [c1lo]; omega)
  have xb3 : x.xb3 < 8 := chunk (k := 3) (by omega) (by omega)
  have xb4 : x.xb4 < 512 := chunk (k := 9) (by omega) (by omega)
  have xb5 : x.xb5 < 16 := chunk (k := 4) (by omega) (by simp only [c1hi]; omega)
  refine ⟨xd0, xd1, xd2, xd3, xb0, xb1, xb2, xb3, xb4, xb5, byte xd2 (by omega),
    byte xd3 (by simp only [a2lo]; omega), byte xd0 (by omega), byte xd1 (by simp only [a2hi]; omega),
    chunk (k := 7) (by omega) (by omega), chunk (k := 9) xb4 (by simp only [c2lo]; omega),
    chunk (k := 7) (by omega) (by omega), chunk (k := 9) xb1 (by simp only [c2hi]; omega)⟩

end RowInput

/-- The row's assignment over the field. -/
def RowInput.assignment {p : Nat} (x : RowInput) (i : Nat) : ZMod p := (x.column i : ZMod p)

namespace RowInput
variable {p : Nat} (x : RowInput)

/-! The honest value of each column, by `rfl` (one lemma per column, for `simp only [honest_column]`). -/

@[honest_column] theorem assignment_0 : x.assignment (p := p) 0 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_1 : x.assignment (p := p) 1 = ((x.invocation : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_2 : x.assignment (p := p) 2 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_3 : x.assignment (p := p) 3 = ((x.control : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_4 : x.assignment (p := p) 4 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_5 : x.assignment (p := p) 5 = ((x.controls[0] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_6 : x.assignment (p := p) 6 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_7 : x.assignment (p := p) 7 = ((x.controls[1] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_8 : x.assignment (p := p) 8 = ((x.controls[2] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_9 : x.assignment (p := p) 9 = ((x.controls[3] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_10 : x.assignment (p := p) 10 = ((x.controls[4] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_11 : x.assignment (p := p) 11 = ((x.controls[5] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_12 : x.assignment (p := p) 12 = ((x.controls[6] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_13 : x.assignment (p := p) 13 = ((x.statePointer.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_14 : x.assignment (p := p) 14 = ((x.statePointer.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_15 : x.assignment (p := p) 15 = ((x.a.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_16 : x.assignment (p := p) 16 = ((x.a.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_17 : x.assignment (p := p) 17 = ((x.a2lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_18 : x.assignment (p := p) 18 = ((x.a2hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_19 : x.assignment (p := p) 19 = ((x.b.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_20 : x.assignment (p := p) 20 = ((x.b.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_21 : x.assignment (p := p) 21 = ((x.b2lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_22 : x.assignment (p := p) 22 = ((x.b2hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_23 : x.assignment (p := p) 23 = ((x.c.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_24 : x.assignment (p := p) 24 = ((x.c.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_25 : x.assignment (p := p) 25 = ((x.c2lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_26 : x.assignment (p := p) 26 = ((x.c2hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_27 : x.assignment (p := p) 27 = ((x.d.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_28 : x.assignment (p := p) 28 = ((x.d.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_29 : x.assignment (p := p) 29 = ((x.d2lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_30 : x.assignment (p := p) 30 = ((x.d2hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_31 : x.assignment (p := p) 31 = ((x.messagePointer.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_32 : x.assignment (p := p) 32 = ((x.messagePointer.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_33 : x.assignment (p := p) 33 = ((x.mx.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_34 : x.assignment (p := p) 34 = ((x.mx.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_35 : x.assignment (p := p) 35 = ((x.my.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_36 : x.assignment (p := p) 36 = ((x.my.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_37 : x.assignment (p := p) 37 = ((x.carryA0 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_38 : x.assignment (p := p) 38 = ((x.carryA0 / 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_39 : x.assignment (p := p) 39 = ((x.carryA1 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_40 : x.assignment (p := p) 40 = ((x.carryA1 / 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_41 : x.assignment (p := p) 41 = ((x.a1lo % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_42 : x.assignment (p := p) 42 = ((x.a1hi % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_43 : x.assignment (p := p) 43 = ((x.d.lo % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_44 : x.assignment (p := p) 44 = ((x.xd0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_45 : x.assignment (p := p) 45 = ((x.xd1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_46 : x.assignment (p := p) 46 = ((x.d.hi % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_47 : x.assignment (p := p) 47 = ((x.xd2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_48 : x.assignment (p := p) 48 = ((x.xd3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_49 : x.assignment (p := p) 49 = ((x.carryC0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_50 : x.assignment (p := p) 50 = ((x.carryC1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_51 : x.assignment (p := p) 51 = ((x.c1lo % 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_52 : x.assignment (p := p) 52 = ((x.c1lo / 8 % 512 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_53 : x.assignment (p := p) 53 = ((x.c1hi % 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_54 : x.assignment (p := p) 54 = ((x.c1hi / 8 % 512 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_55 : x.assignment (p := p) 55 = ((x.b.lo % 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_56 : x.assignment (p := p) 56 = ((x.b.lo / 8 % 512 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_57 : x.assignment (p := p) 57 = ((x.xb0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_58 : x.assignment (p := p) 58 = ((x.xb1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_59 : x.assignment (p := p) 59 = ((x.xb2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_60 : x.assignment (p := p) 60 = ((x.b.hi % 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_61 : x.assignment (p := p) 61 = ((x.b.hi / 8 % 512 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_62 : x.assignment (p := p) 62 = ((x.xb3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_63 : x.assignment (p := p) 63 = ((x.xb4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_64 : x.assignment (p := p) 64 = ((x.xb5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_65 : x.assignment (p := p) 65 = ((x.carryA2 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_66 : x.assignment (p := p) 66 = ((x.carryA2 / 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_67 : x.assignment (p := p) 67 = ((x.carryA3 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_68 : x.assignment (p := p) 68 = ((x.carryA3 / 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_69 : x.assignment (p := p) 69 = ((x.a2lo % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_70 : x.assignment (p := p) 70 = ((x.a2hi % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_71 : x.assignment (p := p) 71 = ((x.xe0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_72 : x.assignment (p := p) 72 = ((x.xe1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_73 : x.assignment (p := p) 73 = ((x.xe2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_74 : x.assignment (p := p) 74 = ((x.xe3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_75 : x.assignment (p := p) 75 = ((x.carryC2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_76 : x.assignment (p := p) 76 = ((x.carryC3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_77 : x.assignment (p := p) 77 = ((x.c2lo % 128 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_78 : x.assignment (p := p) 78 = ((x.c2hi % 128 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_79 : x.assignment (p := p) 79 = ((x.xf0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_80 : x.assignment (p := p) 80 = ((x.xf1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_81 : x.assignment (p := p) 81 = ((x.xf2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_82 : x.assignment (p := p) 82 = ((x.xf3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_83 : x.assignment (p := p) 83 = ((x.previous 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_84 : x.assignment (p := p) 84 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_85 : x.assignment (p := p) 85 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_86 : x.assignment (p := p) 86 = ((x.previous 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_87 : x.assignment (p := p) 87 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_88 : x.assignment (p := p) 88 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_89 : x.assignment (p := p) 89 = ((x.previous 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_90 : x.assignment (p := p) 90 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_91 : x.assignment (p := p) 91 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_92 : x.assignment (p := p) 92 = ((x.previous 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_93 : x.assignment (p := p) 93 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_94 : x.assignment (p := p) 94 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_95 : x.assignment (p := p) 95 = ((x.previous 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_96 : x.assignment (p := p) 96 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_97 : x.assignment (p := p) 97 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_98 : x.assignment (p := p) 98 = ((x.previous 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_99 : x.assignment (p := p) 99 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_100 : x.assignment (p := p) 100 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_101 : x.assignment (p := p) 101 = ((x.previous 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_102 : x.assignment (p := p) 102 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_103 : x.assignment (p := p) 103 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_104 : x.assignment (p := p) 104 = ((x.previous 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_105 : x.assignment (p := p) 105 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_106 : x.assignment (p := p) 106 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_107 : x.assignment (p := p) 107 = ((x.previous 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_108 : x.assignment (p := p) 108 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_109 : x.assignment (p := p) 109 = ((1 : Nat) : ZMod p) := rfl

end RowInput

end Airbender.NonVacuous.Blake2GSpan
