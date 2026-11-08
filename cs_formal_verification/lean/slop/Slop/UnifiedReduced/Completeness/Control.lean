module
public import Slop.UnifiedReduced.Completeness.Frame
public import Slop.UnifiedReduced.Completeness.Rows

@[expose] public section

/-! Completeness of the unified circuit for its control family (JAL, JALR, the SLT
    comparisons and the conditional branches): the honest assignment computed from the
    operands satisfies every equation, range query and setup lookup. Proved once,
    symbolically; only the selector and destination cases are split. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true
set_option maxRecDepth 16384

/-- Inputs of one honest control row. `sel` is 0 (JAL), 1 (JALR), 2 (comparison) or
    3 (branch); `rdZero` marks a discarded destination (always for branches, never for
    comparisons: the decoder admits no SLT* with rd = x0, and constraint 19 would then force
    the flag to 0); `imm*` are the decoder's immediate limbs; `a*`/`b*` are the two register
    operands. -/
structure Control where
  frame : Frame
  sel : Nat
  rdZero : Bool
  funct3 : Nat
  rs1 : Nat
  rs2 : Nat
  rd : Nat
  aLo : Nat
  aHi : Nat
  bLo : Nat
  bHi : Nat
  immLo : Nat
  immHi : Nat
  oldLo : Nat
  oldHi : Nat

namespace Control

def isSel (x : Control) (k : Nat) : Nat := if x.sel = k then 1 else 0
def op2Lo (x : Control) : Nat := x.bLo + if x.sel = 2 then x.immLo else 0
def op2Hi (x : Control) : Nat := x.bHi + if x.sel = 2 then x.immHi else 0
/-- Low limb of the return address (jumps) or of the operand difference. -/
def carryLo (x : Control) : Nat :=
  if x.sel ≤ 1 then (x.frame.pcLo + 4) / 65536 else if x.aLo < x.op2Lo then 1 else 0
def diffLo (x : Control) : Nat :=
  if x.sel ≤ 1 then (x.frame.pcLo + 4) % 65536 else x.aLo + 65536 * x.carryLo - x.op2Lo
def carryHi (x : Control) : Nat :=
  if x.sel ≤ 1 then (x.frame.pcHi + x.carryLo) / 65536
  else if x.aHi < x.op2Hi + x.carryLo then 1 else 0
def diffHi (x : Control) : Nat :=
  if x.sel ≤ 1 then (x.frame.pcHi + x.carryLo) % 65536
  else x.aHi + 65536 * x.carryHi - x.op2Hi - x.carryLo
def zero (x : Control) : Nat := if x.diffLo + x.diffHi = 0 then 1 else 0
def key (x : Control) : Nat :=
  x.op2Hi / 32768 + 2 * (x.aHi / 32768) + 4 * x.carryHi + 8 * x.zero + 16 * x.funct3
/-- The resolved condition, in the setup table's own form. -/
def flag (x : Control) : Nat := conditionalValue (Setup.conditionalKey x.key)
def taken (x : Control) : Nat := if x.sel = 3 then x.flag else 0
def targetLo (x : Control) : Nat :=
  if x.sel = 0 then x.frame.pcLo + x.immLo else if x.sel = 1 then x.aLo + x.immLo
  else if x.taken = 1 then x.frame.pcLo + x.immLo else x.frame.pcLo + 4
def nextLo (x : Control) : Nat := x.targetLo % 65536
def carryNext (x : Control) : Nat := x.targetLo / 65536
def targetHi (x : Control) : Nat :=
  (if x.sel = 0 then x.frame.pcHi + x.immHi else if x.sel = 1 then x.aHi + x.immHi
    else x.frame.pcHi + x.taken * x.immHi) + x.carryNext
def nextHi (x : Control) : Nat := x.targetHi % 65536
def carryHiNext (x : Control) : Nat := x.targetHi / 65536
def misaligned (x : Control) : Nat := x.nextLo / 2 % 2
def aligned (x : Control) : Nat := x.nextLo - x.nextLo % 4
def writesJump (x : Control) : Nat := if x.sel ≤ 1 ∧ x.rdZero = false then 1 else 0
def writesCmp (x : Control) : Nat := if x.sel = 2 ∧ x.rdZero = false then 1 else 0
def rdZeroN (x : Control) : Nat := if x.rdZero then 1 else 0
def outLo (x : Control) : Nat :=
  if x.writesJump = 1 then x.diffLo else if x.writesCmp = 1 then x.flag else 0
def outHi (x : Control) : Nat := if x.writesJump = 1 then x.diffHi else 0

structure Valid (x : Control) : Prop where
  frame : x.frame.Valid
  sel : x.sel ≤ 3
  branch : x.sel = 3 → x.rdZero = true
  comparison : x.sel = 2 → x.rdZero = false
  funct3 : x.funct3 < 8
  rs2 : x.rs2 < 65536
  rd : x.rd < 65536
  aLo : x.aLo < 65536
  aHi : x.aHi < 65536
  immLo : x.immLo < 65536
  immHi : x.immHi < 65536
  op2Lo : x.op2Lo < 65536
  op2Hi : x.op2Hi < 65536
  aligned : x.sel ≤ 1 ∨ x.taken = 1 → x.misaligned = 0

/-- The honest witness columns of a control row. Column 24 is written as the
    complement of the other three selectors so the selector sum is `1` by `ring`. -/
def honest (x : Control) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 => 1
  | 5 => (x.rs1 : Nat)
  | 6 | 38 => (x.rs2 : Nat)
  | 7 | 44 => (x.rd : Nat)
  | 8 => (x.immLo : Nat) | 9 => (x.immHi : Nat)
  | 10 => (x.funct3 : Nat)
  | 21 => (x.isSel 0 : Nat) | 22 => (x.isSel 1 : Nat) | 23 => (x.isSel 2 : Nat)
  | 24 => 1 - (x.isSel 0 : Nat) - (x.isSel 1 : Nat) - (x.isSel 2 : Nat)
  | 25 => (x.rdZeroN : Nat)
  | 30 => (x.aligned : Nat) | 31 => (x.nextHi : Nat)
  | 32 => (x.frame.finalTsLo : Nat) | 33 => (x.frame.finalTsHi : Nat)
  | 34 => (x.frame.prev0Lo : Nat) | 35 => (x.frame.prev0Hi : Nat)
  | 40 => (x.frame.prev1Lo : Nat) | 41 => (x.frame.prev1Hi : Nat)
  | 46 => (x.frame.prev2Lo : Nat) | 47 => (x.frame.prev2Hi : Nat)
  | 36 => (x.aLo : Nat) | 37 | 87 => (x.aHi : Nat)
  | 42 => (x.bLo : Nat) | 43 => (x.bHi : Nat)
  | 48 => (x.oldLo : Nat) | 49 => (x.oldHi : Nat)
  | 50 => (x.outLo : Nat) | 51 => (x.outHi : Nat)
  | 52 => (x.carryLo : Nat) | 53 => (x.carryHi : Nat)
  | 54 => (x.carryNext : Nat) | 55 => (x.carryHiNext : Nat)
  | 56 | 115 => (x.misaligned : Nat)
  | 57 | 84 => (x.zero : Nat)
  | 58 | 88 => (x.aHi / 32768 : Nat)
  | 59 | 106 => (x.flag : Nat)
  | 60 | 96 => (x.op2Hi : Nat) | 61 | 97 => (x.op2Hi / 32768 : Nat)
  | 74 => (x.diffLo : Nat) | 75 => (x.diffHi : Nat)
  | 78 => ((x.aLo : Nat) + 65536 * (x.aHi : Nat)) * ((x.bLo : Nat) + 65536 * (x.bHi : Nat)) * 943718400
  | 64 | 114 => (x.nextLo : Nat)
  | 79 => (x.taken : Nat)
  | 82 => 1
  | 83 => (x.diffLo + x.diffHi : Nat)
  | 86 | 95 => 5
  | 104 => 51
  | 105 => (x.key : Nat)
  | 113 => 2
  | 116 => (x.aligned : Nat)
  | 123 => (x.frame.borrow0 : Nat) | 124 => (x.frame.borrow1 : Nat)
  | 125 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[unified_honest] theorem col_0 (x : Control) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_1 (x : Control) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_2 (x : Control) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_3 (x : Control) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_4 (x : Control) : x.honest 4 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_5 (x : Control) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_6 (x : Control) : x.honest 6 = ((x.rs2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_7 (x : Control) : x.honest 7 = ((x.rd : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_8 (x : Control) : x.honest 8 = ((x.immLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_9 (x : Control) : x.honest 9 = ((x.immHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_10 (x : Control) : x.honest 10 = ((x.funct3 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_11 (x : Control) : x.honest 11 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_12 (x : Control) : x.honest 12 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_13 (x : Control) : x.honest 13 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_14 (x : Control) : x.honest 14 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_15 (x : Control) : x.honest 15 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_16 (x : Control) : x.honest 16 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_17 (x : Control) : x.honest 17 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_18 (x : Control) : x.honest 18 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_19 (x : Control) : x.honest 19 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_20 (x : Control) : x.honest 20 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_21 (x : Control) : x.honest 21 = ((x.isSel 0 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_22 (x : Control) : x.honest 22 = ((x.isSel 1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_23 (x : Control) : x.honest 23 = ((x.isSel 2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_24 (x : Control) : x.honest 24 = (1 - (x.isSel 0 : Nat) - (x.isSel 1 : Nat) - (x.isSel 2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_25 (x : Control) : x.honest 25 = ((x.rdZeroN : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_26 (x : Control) : x.honest 26 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_27 (x : Control) : x.honest 27 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_28 (x : Control) : x.honest 28 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_29 (x : Control) : x.honest 29 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_30 (x : Control) : x.honest 30 = ((x.aligned : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_31 (x : Control) : x.honest 31 = ((x.nextHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_32 (x : Control) : x.honest 32 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_33 (x : Control) : x.honest 33 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_34 (x : Control) : x.honest 34 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_35 (x : Control) : x.honest 35 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_36 (x : Control) : x.honest 36 = ((x.aLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_37 (x : Control) : x.honest 37 = ((x.aHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_38 (x : Control) : x.honest 38 = ((x.rs2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_39 (x : Control) : x.honest 39 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_40 (x : Control) : x.honest 40 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_41 (x : Control) : x.honest 41 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_42 (x : Control) : x.honest 42 = ((x.bLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_43 (x : Control) : x.honest 43 = ((x.bHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_44 (x : Control) : x.honest 44 = ((x.rd : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_45 (x : Control) : x.honest 45 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_46 (x : Control) : x.honest 46 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_47 (x : Control) : x.honest 47 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_48 (x : Control) : x.honest 48 = ((x.oldLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_49 (x : Control) : x.honest 49 = ((x.oldHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_50 (x : Control) : x.honest 50 = ((x.outLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_51 (x : Control) : x.honest 51 = ((x.outHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_52 (x : Control) : x.honest 52 = ((x.carryLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_53 (x : Control) : x.honest 53 = ((x.carryHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_54 (x : Control) : x.honest 54 = ((x.carryNext : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_55 (x : Control) : x.honest 55 = ((x.carryHiNext : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_56 (x : Control) : x.honest 56 = ((x.misaligned : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_57 (x : Control) : x.honest 57 = ((x.zero : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_58 (x : Control) : x.honest 58 = ((x.aHi / 32768 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_59 (x : Control) : x.honest 59 = ((x.flag : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_60 (x : Control) : x.honest 60 = ((x.op2Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_61 (x : Control) : x.honest 61 = ((x.op2Hi / 32768 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_62 (x : Control) : x.honest 62 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_63 (x : Control) : x.honest 63 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_64 (x : Control) : x.honest 64 = ((x.nextLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_65 (x : Control) : x.honest 65 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_66 (x : Control) : x.honest 66 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_67 (x : Control) : x.honest 67 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_68 (x : Control) : x.honest 68 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_69 (x : Control) : x.honest 69 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_70 (x : Control) : x.honest 70 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_71 (x : Control) : x.honest 71 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_72 (x : Control) : x.honest 72 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_73 (x : Control) : x.honest 73 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_74 (x : Control) : x.honest 74 = ((x.diffLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_75 (x : Control) : x.honest 75 = ((x.diffHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_76 (x : Control) : x.honest 76 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_77 (x : Control) : x.honest 77 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_78 (x : Control) : x.honest 78 = (((x.aLo : Nat) + 65536 * (x.aHi : Nat)) * ((x.bLo : Nat) + 65536 * (x.bHi : Nat)) * 943718400 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_79 (x : Control) : x.honest 79 = ((x.taken : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_80 (x : Control) : x.honest 80 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_81 (x : Control) : x.honest 81 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_82 (x : Control) : x.honest 82 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_83 (x : Control) : x.honest 83 = ((x.diffLo + x.diffHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_84 (x : Control) : x.honest 84 = ((x.zero : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_85 (x : Control) : x.honest 85 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_86 (x : Control) : x.honest 86 = (5 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_87 (x : Control) : x.honest 87 = ((x.aHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_88 (x : Control) : x.honest 88 = ((x.aHi / 32768 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_89 (x : Control) : x.honest 89 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_90 (x : Control) : x.honest 90 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_91 (x : Control) : x.honest 91 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_92 (x : Control) : x.honest 92 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_93 (x : Control) : x.honest 93 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_94 (x : Control) : x.honest 94 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_95 (x : Control) : x.honest 95 = (5 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_96 (x : Control) : x.honest 96 = ((x.op2Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_97 (x : Control) : x.honest 97 = ((x.op2Hi / 32768 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_98 (x : Control) : x.honest 98 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_99 (x : Control) : x.honest 99 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_100 (x : Control) : x.honest 100 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_101 (x : Control) : x.honest 101 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_102 (x : Control) : x.honest 102 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_103 (x : Control) : x.honest 103 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_104 (x : Control) : x.honest 104 = (51 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_105 (x : Control) : x.honest 105 = ((x.key : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_106 (x : Control) : x.honest 106 = ((x.flag : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_107 (x : Control) : x.honest 107 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_108 (x : Control) : x.honest 108 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_109 (x : Control) : x.honest 109 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_110 (x : Control) : x.honest 110 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_111 (x : Control) : x.honest 111 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_112 (x : Control) : x.honest 112 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_113 (x : Control) : x.honest 113 = (2 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_114 (x : Control) : x.honest 114 = ((x.nextLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_115 (x : Control) : x.honest 115 = ((x.misaligned : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_116 (x : Control) : x.honest 116 = ((x.aligned : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_117 (x : Control) : x.honest 117 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_118 (x : Control) : x.honest 118 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_119 (x : Control) : x.honest 119 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_120 (x : Control) : x.honest 120 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_121 (x : Control) : x.honest 121 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_122 (x : Control) : x.honest 122 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_123 (x : Control) : x.honest 123 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_124 (x : Control) : x.honest 124 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_125 (x : Control) : x.honest 125 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := by rfl
-- END generated columns

theorem columns (x : Control) : x.frame.Columns x.honest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cast_mod (n d : Nat) :
    ((n % d : Nat) : ZMod babyBearModulus) = (n : ZMod babyBearModulus) - (d : Nat) * ((n / d : Nat) : ZMod babyBearModulus) := by
  have h := congrArg (Nat.cast : Nat → ZMod babyBearModulus) (Nat.mod_add_div n d)
  push_cast at h ⊢
  linear_combination h

theorem bool_of_le {n : Nat} (h : n ≤ 1) :
    (n : ZMod babyBearModulus) * ((n : ZMod babyBearModulus) - 1) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> simp

theorem flag_le (x : Control) : x.flag ≤ 1 := by
  simp only [flag, conditionalValue]; split_ifs <;> omega

theorem taken_le (x : Control) : x.taken ≤ 1 := by
  unfold taken; split
  · exact x.flag_le
  · omega

theorem carryLo_le {x : Control} (hx : x.Valid) : x.carryLo ≤ 1 := by
  have := hx.frame.pcLo; unfold carryLo; split
  · omega
  · split <;> omega

theorem carryHi_le {x : Control} (hx : x.Valid) : x.carryHi ≤ 1 := by
  have hpc := hx.frame.pcHi; have := carryLo_le hx
  unfold Frame.finalPcHi at hpc
  unfold carryHi; split
  · omega
  · split <;> omega

theorem diffLo_lt {x : Control} (hx : x.Valid) : x.diffLo < 65536 := by
  have := hx.op2Lo; have := hx.aLo
  unfold diffLo carryLo; split
  · exact Nat.mod_lt _ (by decide)
  · split <;> omega

theorem diffHi_lt {x : Control} (hx : x.Valid) : x.diffHi < 65536 := by
  have := hx.op2Hi; have := hx.aHi; have := carryLo_le hx
  unfold diffHi carryHi; split
  · exact Nat.mod_lt _ (by decide)
  · split <;> omega

theorem carryNext_le {x : Control} (hx : x.Valid) : x.carryNext ≤ 1 := by
  have := hx.frame.pcLo; have := hx.aLo; have := hx.immLo
  unfold carryNext targetLo; split
  · omega
  · split
    · omega
    · split <;> omega

theorem carryHiNext_le {x : Control} (hx : x.Valid) : x.carryHiNext ≤ 1 := by
  have := hx.frame.pcHi; have := hx.aHi; have := hx.immHi; have := carryNext_le hx
  have := x.taken_le
  unfold Frame.finalPcHi at *
  unfold carryHiNext targetHi; split
  · omega
  · split
    · omega
    · have : x.taken * x.immHi ≤ x.immHi := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp x.taken_le with e | e <;> simp [e]
      omega

theorem diffLo_jump (x : Control) (h : x.sel ≤ 1) :
    (x.diffLo : ZMod babyBearModulus) = (x.frame.pcLo : Nat) + 4 - 65536 * (x.carryLo : Nat) := by
  simp only [diffLo, carryLo, h, ↓reduceIte, cast_mod]; push_cast; ring

theorem diffHi_jump (x : Control) (h : x.sel ≤ 1) :
    (x.diffHi : ZMod babyBearModulus) =
      (x.frame.pcHi : Nat) + (x.carryLo : Nat) - 65536 * (x.carryHi : Nat) := by
  simp only [diffHi, carryHi, h, ↓reduceIte, cast_mod]; push_cast; ring

theorem diffLo_cond {x : Control} (hx : x.Valid) (h : ¬ x.sel ≤ 1) :
    (x.diffLo : ZMod babyBearModulus) = (x.aLo : Nat) + 65536 * (x.carryLo : Nat) - (x.op2Lo : Nat) := by
  have := hx.op2Lo; have := hx.aLo
  simp only [diffLo, carryLo, h, ↓reduceIte]
  split <;> (rw [Nat.cast_sub (by omega)]; push_cast; ring)

theorem diffHi_cond {x : Control} (hx : x.Valid) (h : ¬ x.sel ≤ 1) :
    (x.diffHi : ZMod babyBearModulus) =
      (x.aHi : Nat) + 65536 * (x.carryHi : Nat) - (x.op2Hi : Nat) - (x.carryLo : Nat) := by
  have := hx.op2Hi; have := hx.aHi; have := carryLo_le hx
  simp only [diffHi, carryHi, h, ↓reduceIte]
  split <;> (rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring)

theorem nextLo_eq (x : Control) :
    (x.nextLo : ZMod babyBearModulus) = (x.targetLo : Nat) - 65536 * (x.carryNext : Nat) := by
  simp only [nextLo, carryNext, cast_mod]; push_cast; ring

theorem nextHi_eq (x : Control) :
    (x.nextHi : ZMod babyBearModulus) = (x.targetHi : Nat) - 65536 * (x.carryHiNext : Nat) := by
  simp only [nextHi, carryHiNext, cast_mod]; push_cast; ring

theorem targetLo_branch (x : Control) (h : x.sel = 3) :
    (x.targetLo : ZMod babyBearModulus) =
      (x.frame.pcLo : Nat) + 4 + (x.taken : Nat) * ((x.immLo : Nat) - 4) := by
  have := x.taken_le
  simp only [targetLo, h, Nat.reduceEqDiff, ↓reduceIte]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with e | e <;> simp only [e, ↓reduceIte,
    Nat.reduceEqDiff] <;> push_cast <;> ring

theorem key_eq (x : Control) :
    (x.key : ZMod babyBearModulus) = ((x.op2Hi / 32768 : Nat) : ZMod babyBearModulus) +
      2 * ((x.aHi / 32768 : Nat) : ZMod babyBearModulus) + 4 * (x.carryHi : Nat) + 8 * (x.zero : Nat) +
      16 * (x.funct3 : Nat) := by
  simp only [key]; push_cast; ring

theorem taken_branch (x : Control) (h : x.sel = 3) :
    (x.taken : ZMod babyBearModulus) = (x.flag : Nat) := by
  simp [taken, h]

theorem taken_misaligned {x : Control} (hx : x.Valid) :
    (x.taken : ZMod babyBearModulus) * (x.misaligned : Nat) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp x.taken_le with e | e
  · simp [e]
  · simp [hx.aligned (Or.inr e)]

end Control

end Airbender.UnifiedReduced.Completeness
