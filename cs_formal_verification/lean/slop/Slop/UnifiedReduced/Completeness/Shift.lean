import Slop.UnifiedReduced.Completeness.Frame
import Slop.UnifiedReduced.Completeness.Rows

/-! Completeness of the unified circuit for the shift family (SLL/SRL/SRA, their
    immediate forms, and REV8): the honest assignment built from the operand bytes and
    the table's per-byte contributions satisfies every equation, range query and
    setup lookup. Proved once, symbolically. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true
set_option maxRecDepth 16384

/-- Inputs of one honest shift row. `r*` are the bytes of the second register
    (zero in the immediate form); `payload` is the immediate shift amount. -/
structure Shift where
  frame : Frame
  op : Nat
  immediate : Bool
  payload : Nat
  rs1 : Nat
  rs2 : Nat
  rd : Nat
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  r0 : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat
  oldLo : Nat
  oldHi : Nat

namespace Shift

def amount (x : Shift) : Nat := if x.immediate then x.payload else x.r0 % 32
def part (x : Shift) (i byte : Nat) : Nat → Nat
  | 0 => contribution i byte x.amount x.op % 256
  | 1 => contribution i byte x.amount x.op / 256 % 256
  | 2 => contribution i byte x.amount x.op / 65536 % 256
  | _ => contribution i byte x.amount x.op / 16777216 % 256
def outLo (x : Shift) : Nat :=
  (x.part 0 x.l0 0 + 256 * x.part 0 x.l0 1) + (x.part 1 x.l1 0 + 256 * x.part 1 x.l1 1) +
    (x.part 2 x.l2 0 + 256 * x.part 2 x.l2 1) + (x.part 3 x.l3 0 + 256 * x.part 3 x.l3 1)
def outHi (x : Shift) : Nat :=
  (x.part 0 x.l0 2 + 256 * x.part 0 x.l0 3) + (x.part 1 x.l1 2 + 256 * x.part 1 x.l1 3) +
    (x.part 2 x.l2 2 + 256 * x.part 2 x.l2 3) + (x.part 3 x.l3 2 + 256 * x.part 3 x.l3 3)

structure Valid (x : Shift) : Prop where
  frame : x.frame.Valid
  op : x.op < 8
  payload : x.payload < 32
  rs2 : x.rs2 < 65536
  rd : x.rd < 65536
  l0 : x.l0 < 256
  l1 : x.l1 < 256
  l2 : x.l2 < 256
  l3 : x.l3 < 256
  r0 : x.r0 < 256
  r1 : x.r1 < 256
  r2 : x.r2 < 256
  r3 : x.r3 < 256
  outLo : x.outLo < 65536
  outHi : x.outHi < 65536

/-- The honest witness columns of a shift row. -/
def honest (x : Shift) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 | 26 => 1
  | 5 => (x.rs1 : Nat)
  | 6 | 38 => (x.rs2 : Nat)
  | 7 | 44 => (x.rd : Nat)
  | 8 => if x.immediate then (x.payload : Nat) else 0
  | 10 | 90 | 99 | 108 | 117 => (x.op : Nat)
  | 30 => (x.frame.finalPcLo : Nat) | 31 => (x.frame.finalPcHi : Nat)
  | 32 => (x.frame.finalTsLo : Nat) | 33 => (x.frame.finalTsHi : Nat)
  | 34 => (x.frame.prev0Lo : Nat) | 35 => (x.frame.prev0Hi : Nat)
  | 40 => (x.frame.prev1Lo : Nat) | 41 => (x.frame.prev1Hi : Nat)
  | 46 => (x.frame.prev2Lo : Nat) | 47 => (x.frame.prev2Hi : Nat)
  | 36 => (x.l0 + 256 * x.l1 : Nat) | 37 => (x.l2 + 256 * x.l3 : Nat)
  | 42 => if x.immediate then 0 else (x.r0 + 256 * x.r1 : Nat)
  | 43 => if x.immediate then 0 else (x.r2 + 256 * x.r3 : Nat)
  | 48 => (x.oldLo : Nat) | 49 => (x.oldHi : Nat)
  | 50 => (x.outLo : Nat) | 51 => (x.outHi : Nat)
  | 57 | 85 => if x.immediate then 0 else (x.r0 % 32 : Nat)
  | 74 | 88 => (x.l0 : Nat) | 75 | 106 => (x.l2 : Nat)
  | 76 | 83 => if x.immediate then 0 else (x.r0 : Nat)
  | 84 => if x.immediate then 0 else (x.r1 : Nat)
  | 97 => (x.l1 : Nat) | 115 => (x.l3 : Nat)
  | 89 | 98 | 107 | 116 => (x.amount : Nat)
  | 86 | 95 | 104 | 113 => 9
  | 96 => 1 | 105 => 2 | 114 => 3
  | 58 | 91 => (x.part 0 x.l0 0 : Nat) | 59 | 92 => (x.part 0 x.l0 1 : Nat)
  | 60 | 93 => (x.part 0 x.l0 2 : Nat) | 61 | 94 => (x.part 0 x.l0 3 : Nat)
  | 62 | 100 => (x.part 1 x.l1 0 : Nat) | 63 | 101 => (x.part 1 x.l1 1 : Nat)
  | 64 | 102 => (x.part 1 x.l1 2 : Nat) | 65 | 103 => (x.part 1 x.l1 3 : Nat)
  | 66 | 109 => (x.part 2 x.l2 0 : Nat) | 67 | 110 => (x.part 2 x.l2 1 : Nat)
  | 68 | 111 => (x.part 2 x.l2 2 : Nat) | 69 | 112 => (x.part 2 x.l2 3 : Nat)
  | 70 | 118 => (x.part 3 x.l3 0 : Nat) | 71 | 119 => (x.part 3 x.l3 1 : Nat)
  | 72 | 120 => (x.part 3 x.l3 2 : Nat) | 73 | 121 => (x.part 3 x.l3 3 : Nat)
  | 78 => ((x.l0 + 256 * x.l1 : Nat) + 65536 * (x.l2 + 256 * x.l3 : Nat)) *
      ((if x.immediate then 0 else (x.r0 + 256 * x.r1 : Nat)) +
        65536 * (if x.immediate then 0 else (x.r2 + 256 * x.r3 : Nat))) * 943718400
  | 82 => 8
  | 122 => (x.frame.pcCarry : Nat)
  | 123 => (x.frame.borrow0 : Nat) | 124 => (x.frame.borrow1 : Nat)
  | 125 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[unified_honest] theorem col_0 (x : Shift) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_1 (x : Shift) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_2 (x : Shift) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_3 (x : Shift) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_4 (x : Shift) : x.honest 4 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_5 (x : Shift) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_6 (x : Shift) : x.honest 6 = ((x.rs2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_7 (x : Shift) : x.honest 7 = ((x.rd : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_8 (x : Shift) : x.honest 8 = (if x.immediate then (x.payload : Nat) else 0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_9 (x : Shift) : x.honest 9 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_10 (x : Shift) : x.honest 10 = ((x.op : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_11 (x : Shift) : x.honest 11 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_12 (x : Shift) : x.honest 12 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_13 (x : Shift) : x.honest 13 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_14 (x : Shift) : x.honest 14 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_15 (x : Shift) : x.honest 15 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_16 (x : Shift) : x.honest 16 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_17 (x : Shift) : x.honest 17 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_18 (x : Shift) : x.honest 18 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_19 (x : Shift) : x.honest 19 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_20 (x : Shift) : x.honest 20 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_21 (x : Shift) : x.honest 21 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_22 (x : Shift) : x.honest 22 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_23 (x : Shift) : x.honest 23 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_24 (x : Shift) : x.honest 24 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_25 (x : Shift) : x.honest 25 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_26 (x : Shift) : x.honest 26 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_27 (x : Shift) : x.honest 27 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_28 (x : Shift) : x.honest 28 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_29 (x : Shift) : x.honest 29 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_30 (x : Shift) : x.honest 30 = ((x.frame.finalPcLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_31 (x : Shift) : x.honest 31 = ((x.frame.finalPcHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_32 (x : Shift) : x.honest 32 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_33 (x : Shift) : x.honest 33 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_34 (x : Shift) : x.honest 34 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_35 (x : Shift) : x.honest 35 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_36 (x : Shift) : x.honest 36 = ((x.l0 + 256 * x.l1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_37 (x : Shift) : x.honest 37 = ((x.l2 + 256 * x.l3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_38 (x : Shift) : x.honest 38 = ((x.rs2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_39 (x : Shift) : x.honest 39 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_40 (x : Shift) : x.honest 40 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_41 (x : Shift) : x.honest 41 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_42 (x : Shift) : x.honest 42 = (if x.immediate then 0 else (x.r0 + 256 * x.r1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_43 (x : Shift) : x.honest 43 = (if x.immediate then 0 else (x.r2 + 256 * x.r3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_44 (x : Shift) : x.honest 44 = ((x.rd : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_45 (x : Shift) : x.honest 45 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_46 (x : Shift) : x.honest 46 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_47 (x : Shift) : x.honest 47 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_48 (x : Shift) : x.honest 48 = ((x.oldLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_49 (x : Shift) : x.honest 49 = ((x.oldHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_50 (x : Shift) : x.honest 50 = ((x.outLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_51 (x : Shift) : x.honest 51 = ((x.outHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_52 (x : Shift) : x.honest 52 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_53 (x : Shift) : x.honest 53 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_54 (x : Shift) : x.honest 54 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_55 (x : Shift) : x.honest 55 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_56 (x : Shift) : x.honest 56 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_57 (x : Shift) : x.honest 57 = (if x.immediate then 0 else (x.r0 % 32 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_58 (x : Shift) : x.honest 58 = ((x.part 0 x.l0 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_59 (x : Shift) : x.honest 59 = ((x.part 0 x.l0 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_60 (x : Shift) : x.honest 60 = ((x.part 0 x.l0 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_61 (x : Shift) : x.honest 61 = ((x.part 0 x.l0 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_62 (x : Shift) : x.honest 62 = ((x.part 1 x.l1 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_63 (x : Shift) : x.honest 63 = ((x.part 1 x.l1 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_64 (x : Shift) : x.honest 64 = ((x.part 1 x.l1 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_65 (x : Shift) : x.honest 65 = ((x.part 1 x.l1 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_66 (x : Shift) : x.honest 66 = ((x.part 2 x.l2 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_67 (x : Shift) : x.honest 67 = ((x.part 2 x.l2 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_68 (x : Shift) : x.honest 68 = ((x.part 2 x.l2 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_69 (x : Shift) : x.honest 69 = ((x.part 2 x.l2 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_70 (x : Shift) : x.honest 70 = ((x.part 3 x.l3 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_71 (x : Shift) : x.honest 71 = ((x.part 3 x.l3 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_72 (x : Shift) : x.honest 72 = ((x.part 3 x.l3 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_73 (x : Shift) : x.honest 73 = ((x.part 3 x.l3 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_74 (x : Shift) : x.honest 74 = ((x.l0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_75 (x : Shift) : x.honest 75 = ((x.l2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_76 (x : Shift) : x.honest 76 = (if x.immediate then 0 else (x.r0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_77 (x : Shift) : x.honest 77 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_78 (x : Shift) : x.honest 78 = (((x.l0 + 256 * x.l1 : Nat) + 65536 * (x.l2 + 256 * x.l3 : Nat)) * ((if x.immediate then 0 else (x.r0 + 256 * x.r1 : Nat)) + 65536 * (if x.immediate then 0 else (x.r2 + 256 * x.r3 : Nat))) * 943718400 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_79 (x : Shift) : x.honest 79 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_80 (x : Shift) : x.honest 80 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_81 (x : Shift) : x.honest 81 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_82 (x : Shift) : x.honest 82 = (8 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_83 (x : Shift) : x.honest 83 = (if x.immediate then 0 else (x.r0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_84 (x : Shift) : x.honest 84 = (if x.immediate then 0 else (x.r1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_85 (x : Shift) : x.honest 85 = (if x.immediate then 0 else (x.r0 % 32 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_86 (x : Shift) : x.honest 86 = (9 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_87 (x : Shift) : x.honest 87 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_88 (x : Shift) : x.honest 88 = ((x.l0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_89 (x : Shift) : x.honest 89 = ((x.amount : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_90 (x : Shift) : x.honest 90 = ((x.op : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_91 (x : Shift) : x.honest 91 = ((x.part 0 x.l0 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_92 (x : Shift) : x.honest 92 = ((x.part 0 x.l0 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_93 (x : Shift) : x.honest 93 = ((x.part 0 x.l0 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_94 (x : Shift) : x.honest 94 = ((x.part 0 x.l0 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_95 (x : Shift) : x.honest 95 = (9 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_96 (x : Shift) : x.honest 96 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_97 (x : Shift) : x.honest 97 = ((x.l1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_98 (x : Shift) : x.honest 98 = ((x.amount : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_99 (x : Shift) : x.honest 99 = ((x.op : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_100 (x : Shift) : x.honest 100 = ((x.part 1 x.l1 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_101 (x : Shift) : x.honest 101 = ((x.part 1 x.l1 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_102 (x : Shift) : x.honest 102 = ((x.part 1 x.l1 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_103 (x : Shift) : x.honest 103 = ((x.part 1 x.l1 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_104 (x : Shift) : x.honest 104 = (9 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_105 (x : Shift) : x.honest 105 = (2 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_106 (x : Shift) : x.honest 106 = ((x.l2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_107 (x : Shift) : x.honest 107 = ((x.amount : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_108 (x : Shift) : x.honest 108 = ((x.op : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_109 (x : Shift) : x.honest 109 = ((x.part 2 x.l2 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_110 (x : Shift) : x.honest 110 = ((x.part 2 x.l2 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_111 (x : Shift) : x.honest 111 = ((x.part 2 x.l2 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_112 (x : Shift) : x.honest 112 = ((x.part 2 x.l2 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_113 (x : Shift) : x.honest 113 = (9 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_114 (x : Shift) : x.honest 114 = (3 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_115 (x : Shift) : x.honest 115 = ((x.l3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_116 (x : Shift) : x.honest 116 = ((x.amount : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_117 (x : Shift) : x.honest 117 = ((x.op : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_118 (x : Shift) : x.honest 118 = ((x.part 3 x.l3 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_119 (x : Shift) : x.honest 119 = ((x.part 3 x.l3 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_120 (x : Shift) : x.honest 120 = ((x.part 3 x.l3 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_121 (x : Shift) : x.honest 121 = ((x.part 3 x.l3 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_122 (x : Shift) : x.honest 122 = ((x.frame.pcCarry : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_123 (x : Shift) : x.honest 123 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_124 (x : Shift) : x.honest 124 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_125 (x : Shift) : x.honest 125 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := rfl
-- END generated columns

/-- The third byte of a contribution (range-checked through the shared scratch column 64). -/
theorem part_two_lt (x : Shift) (i byte : Nat) : x.part i byte 2 < 256 := by
  simp only [part]; omega

theorem columns (x : Shift) : x.frame.Columns x.honest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Shift

end Airbender.UnifiedReduced.Completeness
