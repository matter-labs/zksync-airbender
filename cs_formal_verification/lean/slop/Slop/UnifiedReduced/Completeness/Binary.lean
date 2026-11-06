import Slop.UnifiedReduced.Completeness.Frame
import Slop.UnifiedReduced.Completeness.Rows

/-! Completeness of the unified circuit for its byte-pair family (XOR/OR/AND, their
    immediate forms, and XOR-rotate): the honest assignment computed from bytes satisfies
    every retained equation, range query and setup lookup. Proved once, symbolically. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true
set_option maxRecDepth 16384

/-- Inputs of one honest row of the wide byte-pair family: XOR/OR/AND (register or
    immediate form, `r*` the sign-extended immediate bytes in the latter) and the
    XOR-rotate rows (`rotation`, amount index `k`). -/
structure Binary where
  frame : Frame
  tag : Nat
  rotation : Bool
  k : Nat
  immediate : Bool
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

namespace Binary

def left (x : Binary) : Nat → Nat
  | 0 => x.l0 | 1 => x.l1 | 2 => x.l2 | _ => x.l3
def right (x : Binary) : Nat → Nat
  | 0 => x.r0 | 1 => x.r1 | 2 => x.r2 | _ => x.r3

/-- Output slot `j` of byte pair `i`, in the setup table's own form. -/
def slot (x : Binary) (i j : Nat) : Nat :=
  if x.rotation then rotated x.k (x.left i) (x.right i) j
  else if j = 0 then byteOp x.tag (x.left i) (x.right i) else 0

/-- The ID column of the byte-pair queries. -/
def tagColumn (x : Binary) : Nat := if x.rotation then 47 + x.k else Setup.binaryTag x.tag

def outLo (x : Binary) : Nat :=
  (x.slot 0 0 + 256 * x.slot 0 1) + (x.slot 1 3 + 256 * x.slot 1 0) +
    (x.slot 2 2 + 256 * x.slot 2 3) + (x.slot 3 1 + 256 * x.slot 3 2)
def outHi (x : Binary) : Nat :=
  (x.slot 0 2 + 256 * x.slot 0 3) + (x.slot 1 1 + 256 * x.slot 1 2) +
    (x.slot 2 0 + 256 * x.slot 2 1) + (x.slot 3 3 + 256 * x.slot 3 0)

structure Valid (x : Binary) : Prop where
  frame : x.frame.Valid
  tag : x.rotation = false → x.tag = 4 ∨ x.tag = 6 ∨ x.tag = 7
  k : x.rotation = true → x.k < 4
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
  sign : x.immediate = true → x.r2 = (if x.r1 < 128 then 0 else 255) ∧ x.r3 = x.r2
  outLo : x.outLo < 65536
  outHi : x.outHi < 65536

/-- The honest witness columns of a binary row. -/
def honest (x : Binary) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 | 27 | 129 | 130 => 1
  | 5 => (x.rs1 : Nat)
  | 6 | 38 => (x.rs2 : Nat)
  | 7 | 44 => (x.rd : Nat)
  | 8 => if x.immediate then (x.r0 : Nat) else 0
  | 9 | 89 => if x.immediate then (x.r1 : Nat) else 0
  | 10 | 92 | 101 | 110 | 119 => (x.tagColumn : Nat)
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
  | 57 | 90 => if x.immediate then (x.r2 : Nat) else 0
  | 58 | 95 => (x.slot 0 0 : Nat) | 59 | 96 => (x.slot 0 1 : Nat)
  | 60 | 97 => (x.slot 0 2 : Nat) | 61 | 98 => (x.slot 0 3 : Nat)
  | 62 | 104 => (x.slot 1 0 : Nat) | 63 | 105 => (x.slot 1 1 : Nat)
  | 64 | 106 => (x.slot 1 2 : Nat) | 65 | 107 => (x.slot 1 3 : Nat)
  | 66 | 113 => (x.slot 2 0 : Nat) | 67 | 114 => (x.slot 2 1 : Nat)
  | 68 | 115 => (x.slot 2 2 : Nat) | 69 | 116 => (x.slot 2 3 : Nat)
  | 70 | 122 => (x.slot 3 0 : Nat) | 71 | 123 => (x.slot 3 1 : Nat)
  | 72 | 124 => (x.slot 3 2 : Nat) | 73 | 125 => (x.slot 3 3 : Nat)
  | 74 | 93 => (x.l0 : Nat) | 75 | 111 => (x.l2 : Nat)
  | 76 => if x.immediate then 0 else (x.r0 : Nat)
  | 77 => if x.immediate then 0 else (x.r2 : Nat)
  | 94 => (x.r0 : Nat) | 102 => (x.l1 : Nat) | 103 => (x.r1 : Nat)
  | 112 => (x.r2 : Nat) | 120 => (x.l3 : Nat) | 121 => (x.r3 : Nat)
  | 80 => ((x.l0 + 256 * x.l1 : Nat) + 65536 * (x.l2 + 256 * x.l3 : Nat)) *
      ((if x.immediate then 0 else (x.r0 + 256 * x.r1 : Nat)) +
        65536 * (if x.immediate then 0 else (x.r2 + 256 * x.r3 : Nat))) * 943718400
  | 88 => 3
  | 128 => (x.frame.pcCarry : Nat)
  | 131 => (x.frame.borrow0 : Nat) | 132 => (x.frame.borrow1 : Nat)
  | 133 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[unified_honest] theorem col_0 (x : Binary) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_1 (x : Binary) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_2 (x : Binary) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_3 (x : Binary) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_4 (x : Binary) : x.honest 4 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_5 (x : Binary) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_6 (x : Binary) : x.honest 6 = ((x.rs2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_7 (x : Binary) : x.honest 7 = ((x.rd : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_8 (x : Binary) : x.honest 8 = (if x.immediate then (x.r0 : Nat) else 0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_9 (x : Binary) : x.honest 9 = (if x.immediate then (x.r1 : Nat) else 0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_10 (x : Binary) : x.honest 10 = ((x.tagColumn : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_11 (x : Binary) : x.honest 11 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_12 (x : Binary) : x.honest 12 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_13 (x : Binary) : x.honest 13 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_14 (x : Binary) : x.honest 14 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_15 (x : Binary) : x.honest 15 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_16 (x : Binary) : x.honest 16 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_17 (x : Binary) : x.honest 17 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_18 (x : Binary) : x.honest 18 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_19 (x : Binary) : x.honest 19 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_20 (x : Binary) : x.honest 20 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_21 (x : Binary) : x.honest 21 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_22 (x : Binary) : x.honest 22 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_23 (x : Binary) : x.honest 23 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_24 (x : Binary) : x.honest 24 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_25 (x : Binary) : x.honest 25 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_26 (x : Binary) : x.honest 26 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_27 (x : Binary) : x.honest 27 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_28 (x : Binary) : x.honest 28 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_29 (x : Binary) : x.honest 29 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_30 (x : Binary) : x.honest 30 = ((x.frame.finalPcLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_31 (x : Binary) : x.honest 31 = ((x.frame.finalPcHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_32 (x : Binary) : x.honest 32 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_33 (x : Binary) : x.honest 33 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_34 (x : Binary) : x.honest 34 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_35 (x : Binary) : x.honest 35 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_36 (x : Binary) : x.honest 36 = ((x.l0 + 256 * x.l1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_37 (x : Binary) : x.honest 37 = ((x.l2 + 256 * x.l3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_38 (x : Binary) : x.honest 38 = ((x.rs2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_39 (x : Binary) : x.honest 39 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_40 (x : Binary) : x.honest 40 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_41 (x : Binary) : x.honest 41 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_42 (x : Binary) : x.honest 42 = (if x.immediate then 0 else (x.r0 + 256 * x.r1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_43 (x : Binary) : x.honest 43 = (if x.immediate then 0 else (x.r2 + 256 * x.r3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_44 (x : Binary) : x.honest 44 = ((x.rd : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_45 (x : Binary) : x.honest 45 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_46 (x : Binary) : x.honest 46 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_47 (x : Binary) : x.honest 47 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_48 (x : Binary) : x.honest 48 = ((x.oldLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_49 (x : Binary) : x.honest 49 = ((x.oldHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_50 (x : Binary) : x.honest 50 = ((x.outLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_51 (x : Binary) : x.honest 51 = ((x.outHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_52 (x : Binary) : x.honest 52 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_53 (x : Binary) : x.honest 53 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_54 (x : Binary) : x.honest 54 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_55 (x : Binary) : x.honest 55 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_56 (x : Binary) : x.honest 56 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_57 (x : Binary) : x.honest 57 = (if x.immediate then (x.r2 : Nat) else 0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_58 (x : Binary) : x.honest 58 = ((x.slot 0 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_59 (x : Binary) : x.honest 59 = ((x.slot 0 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_60 (x : Binary) : x.honest 60 = ((x.slot 0 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_61 (x : Binary) : x.honest 61 = ((x.slot 0 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_62 (x : Binary) : x.honest 62 = ((x.slot 1 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_63 (x : Binary) : x.honest 63 = ((x.slot 1 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_64 (x : Binary) : x.honest 64 = ((x.slot 1 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_65 (x : Binary) : x.honest 65 = ((x.slot 1 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_66 (x : Binary) : x.honest 66 = ((x.slot 2 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_67 (x : Binary) : x.honest 67 = ((x.slot 2 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_68 (x : Binary) : x.honest 68 = ((x.slot 2 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_69 (x : Binary) : x.honest 69 = ((x.slot 2 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_70 (x : Binary) : x.honest 70 = ((x.slot 3 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_71 (x : Binary) : x.honest 71 = ((x.slot 3 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_72 (x : Binary) : x.honest 72 = ((x.slot 3 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_73 (x : Binary) : x.honest 73 = ((x.slot 3 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_74 (x : Binary) : x.honest 74 = ((x.l0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_75 (x : Binary) : x.honest 75 = ((x.l2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_76 (x : Binary) : x.honest 76 = (if x.immediate then 0 else (x.r0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_77 (x : Binary) : x.honest 77 = (if x.immediate then 0 else (x.r2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_78 (x : Binary) : x.honest 78 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_79 (x : Binary) : x.honest 79 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_80 (x : Binary) : x.honest 80 = (((x.l0 + 256 * x.l1 : Nat) + 65536 * (x.l2 + 256 * x.l3 : Nat)) * ((if x.immediate then 0 else (x.r0 + 256 * x.r1 : Nat)) + 65536 * (if x.immediate then 0 else (x.r2 + 256 * x.r3 : Nat))) * 943718400 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_81 (x : Binary) : x.honest 81 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_82 (x : Binary) : x.honest 82 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_83 (x : Binary) : x.honest 83 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_84 (x : Binary) : x.honest 84 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_85 (x : Binary) : x.honest 85 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_86 (x : Binary) : x.honest 86 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_87 (x : Binary) : x.honest 87 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_88 (x : Binary) : x.honest 88 = (3 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_89 (x : Binary) : x.honest 89 = (if x.immediate then (x.r1 : Nat) else 0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_90 (x : Binary) : x.honest 90 = (if x.immediate then (x.r2 : Nat) else 0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_91 (x : Binary) : x.honest 91 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_92 (x : Binary) : x.honest 92 = ((x.tagColumn : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_93 (x : Binary) : x.honest 93 = ((x.l0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_94 (x : Binary) : x.honest 94 = ((x.r0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_95 (x : Binary) : x.honest 95 = ((x.slot 0 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_96 (x : Binary) : x.honest 96 = ((x.slot 0 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_97 (x : Binary) : x.honest 97 = ((x.slot 0 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_98 (x : Binary) : x.honest 98 = ((x.slot 0 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_99 (x : Binary) : x.honest 99 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_100 (x : Binary) : x.honest 100 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_101 (x : Binary) : x.honest 101 = ((x.tagColumn : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_102 (x : Binary) : x.honest 102 = ((x.l1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_103 (x : Binary) : x.honest 103 = ((x.r1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_104 (x : Binary) : x.honest 104 = ((x.slot 1 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_105 (x : Binary) : x.honest 105 = ((x.slot 1 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_106 (x : Binary) : x.honest 106 = ((x.slot 1 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_107 (x : Binary) : x.honest 107 = ((x.slot 1 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_108 (x : Binary) : x.honest 108 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_109 (x : Binary) : x.honest 109 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_110 (x : Binary) : x.honest 110 = ((x.tagColumn : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_111 (x : Binary) : x.honest 111 = ((x.l2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_112 (x : Binary) : x.honest 112 = ((x.r2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_113 (x : Binary) : x.honest 113 = ((x.slot 2 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_114 (x : Binary) : x.honest 114 = ((x.slot 2 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_115 (x : Binary) : x.honest 115 = ((x.slot 2 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_116 (x : Binary) : x.honest 116 = ((x.slot 2 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_117 (x : Binary) : x.honest 117 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_118 (x : Binary) : x.honest 118 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_119 (x : Binary) : x.honest 119 = ((x.tagColumn : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_120 (x : Binary) : x.honest 120 = ((x.l3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_121 (x : Binary) : x.honest 121 = ((x.r3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_122 (x : Binary) : x.honest 122 = ((x.slot 3 0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_123 (x : Binary) : x.honest 123 = ((x.slot 3 1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_124 (x : Binary) : x.honest 124 = ((x.slot 3 2 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_125 (x : Binary) : x.honest 125 = ((x.slot 3 3 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_126 (x : Binary) : x.honest 126 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_127 (x : Binary) : x.honest 127 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_128 (x : Binary) : x.honest 128 = ((x.frame.pcCarry : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_129 (x : Binary) : x.honest 129 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_130 (x : Binary) : x.honest 130 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_131 (x : Binary) : x.honest 131 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_132 (x : Binary) : x.honest 132 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_133 (x : Binary) : x.honest 133 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := rfl
-- END generated columns

theorem columns (x : Binary) : x.frame.Columns x.honest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem complete (x : Binary) (hx : x.Valid) (before : Reference.RiscV.Sail.State) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest)
      (clockConstraints (Setup.table before)) := by
  refine holds_append ?_ (Frame.timestamps hx.frame x.columns)
  have hf := hx.frame
  have hl0 := hx.l0; have hl1 := hx.l1; have hl2 := hx.l2; have hl3 := hx.l3
  have hr0 := hx.r0; have hr1 := hx.r1; have hr2 := hx.r2; have hr3 := hx.r3
  have := hx.outLo; have := hx.outHi; have := hx.rs2; have := hx.rd; have := hf.pcHi
  have : x.frame.pcHi < 65536 := by have := hf.pcHi; unfold Frame.finalPcHi at this; omega
  have : x.frame.finalPcLo < 65536 := Nat.mod_lt _ (by decide)
  have hoff : (if x.tag = 4 then 257 else if x.tag = 6 then 65793 else 131329) + 255 * 256 + 255 <
      2097537 := by split_ifs <;> omega
  have hk : x.rotation = true → 786817 + x.k * 65536 + 255 * 256 + 255 < 2097537 := fun h => by
    have := hx.k h; omega
  simp only [importedConstraints, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  -- goals 1-129: equations; 130-142: 16-bit ranges; 143-147: setup lookups
  on_goal 143 =>
    cases himm : x.immediate
    · refine table_contains_row ⟨1 + 0, by omega⟩ _ (sign_row before 0 (by omega))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, himm]
    · obtain ⟨h2, -⟩ := hx.sign himm
      refine table_contains_row ⟨1 + x.r1, by omega⟩ _ (sign_row before x.r1 hr1)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, himm, h2]
  on_goal 143 =>
    cases hrot : x.rotation
    · refine table_contains_row ⟨_, by omega⟩ _
        (binary_row before x.tag x.l0 x.r0 (hx.tag hrot) hl0 hr0 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
    · have := hk hrot
      refine table_contains_row ⟨_, by omega⟩ _
        (rotate_row before x.k x.l0 x.r0 (hx.k hrot) hl0 hr0 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
  on_goal 143 =>
    cases hrot : x.rotation
    · refine table_contains_row ⟨_, by omega⟩ _
        (binary_row before x.tag x.l1 x.r1 (hx.tag hrot) hl1 hr1 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
    · have := hk hrot
      refine table_contains_row ⟨_, by omega⟩ _
        (rotate_row before x.k x.l1 x.r1 (hx.k hrot) hl1 hr1 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
  on_goal 143 =>
    cases hrot : x.rotation
    · refine table_contains_row ⟨_, by omega⟩ _
        (binary_row before x.tag x.l2 x.r2 (hx.tag hrot) hl2 hr2 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
    · have := hk hrot
      refine table_contains_row ⟨_, by omega⟩ _
        (rotate_row before x.k x.l2 x.r2 (hx.k hrot) hl2 hr2 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
  on_goal 143 =>
    cases hrot : x.rotation
    · refine table_contains_row ⟨_, by omega⟩ _
        (binary_row before x.tag x.l3 x.r3 (hx.tag hrot) hl3 hr3 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
    · have := hk hrot
      refine table_contains_row ⟨_, by omega⟩ _
        (rotate_row before x.k x.l3 x.r3 (hx.k hrot) hl3 hr3 _ rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp [Expression.eval, environment, unified_honest, slot, tagColumn, hrot, left, right]
  all_goals first
    | exact True.intro
    | (apply range16_contains
       simp only [Expression.eval, environment, unified_honest, cast_ofNat, Nat.cast_zero, Nat.cast_one,
         zero_add, one_mul, Arithmetic.limbBase]
       first
         | (rw [ZMod.val_natCast]; exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega))
         | (simp only [ZMod.val_zero]; decide))
    | skip
  all_goals simp only [Expression.eval, environment, unified_honest, cast_ofNat, cast_negSucc,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul,
    add_zero, zero_add, mul_one, one_mul, outLo, outHi]
  all_goals first
    | done
    | ring1
    | linear_combination x.frame.pc_low
    | linear_combination -x.frame.pc_high
    | linear_combination x.frame.ts_square hf.clock
    | linear_combination x.frame.ts_high
    | linear_combination Frame.pcCarry_bool hf.clock
    | linear_combination x.frame.borrow0_bool
    | linear_combination x.frame.borrow1_bool
    | linear_combination x.frame.borrow2_bool
    | linear_combination (-(x.l1 : ZMod babyBearModulus)) * inv256
    | linear_combination (-(x.l3 : ZMod babyBearModulus)) * inv256
    | linear_combination (-(x.r1 : ZMod babyBearModulus)) * inv256
    | linear_combination (-(x.r3 : ZMod babyBearModulus)) * inv256
    | (cases himm : x.immediate
       all_goals simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_zero,
         mul_zero, zero_mul, add_zero, zero_add]
       all_goals first
         | done
         | ring1
         | linear_combination x.frame.pc_low
         | linear_combination -x.frame.pc_high
         | linear_combination x.frame.ts_square hf.clock
         | linear_combination x.frame.ts_high
         | linear_combination Frame.pcCarry_bool hf.clock
         | linear_combination x.frame.borrow0_bool
         | linear_combination x.frame.borrow1_bool
         | linear_combination x.frame.borrow2_bool
         | linear_combination (-(x.l1 : ZMod babyBearModulus)) * inv256
         | linear_combination (-(x.l3 : ZMod babyBearModulus)) * inv256
         | linear_combination (-(x.r1 : ZMod babyBearModulus)) * inv256
         | linear_combination (-(x.r3 : ZMod babyBearModulus)) * inv256
         | (obtain ⟨-, h3⟩ := hx.sign himm
            rw [h3]; ring1))

end Binary

end Airbender.UnifiedReduced.Completeness
