module
public import Slop.UnifiedReduced.Completeness.Frame
public import Slop.UnifiedReduced.Completeness.Rows

@[expose] public section

/-! Completeness of the unified circuit for its additive family (ADD/ADDI, SUB, AUIPC and
    the three-operand TriAdd row): the honest assignment satisfies every equation, range
    query and setup lookup, for any setup table holding the disabled all-zero query.
    Proved once, symbolically; only the selector case is split. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true
set_option maxRecDepth 16384

/-- The setup table answers the disabled all-zero query. -/
def ZeroRow (t : Table (ZMod babyBearModulus) (fields 10)) : Prop :=
  ∀ (env : Environment (ZMod babyBearModulus)) (entry : Vector (Expression (ZMod babyBearModulus)) 10),
    entry.map (Expression.eval env) = Vector.replicate 10 0 → (Lookup.mk t.toRaw entry).Contains env

/-- Inputs of one honest additive row: `sel` is 0 (ADD/ADDI), 1 (SUB), 2 (AUIPC) or
    3 (TriAdd, which adds the old destination value). -/
structure Arith where
  frame : Frame
  sel : Nat
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

namespace Arith

def isSel (x : Arith) (k : Nat) : Nat := if x.sel = k then 1 else 0
def sumLo (x : Arith) : Nat :=
  if x.sel = 2 then x.frame.pcLo + x.immLo
  else if x.sel = 3 then x.aLo + x.bLo + x.oldLo else x.aLo + x.bLo + x.immLo
def carryLo (x : Arith) : Nat :=
  if x.sel = 1 then (if x.aLo < x.bLo then 1 else 0)
  else if x.sel = 3 then (if 65536 ≤ x.sumLo then 1 else 0) else x.sumLo / 65536
def carryLo2 (x : Arith) : Nat := if x.sel = 3 ∧ 131072 ≤ x.sumLo then 1 else 0
def outLo (x : Arith) : Nat :=
  if x.sel = 1 then x.aLo + 65536 * x.carryLo - x.bLo else x.sumLo % 65536
def sumHi (x : Arith) : Nat :=
  if x.sel = 2 then x.carryLo + x.frame.pcHi + x.immHi
  else if x.sel = 3 then x.carryLo + x.carryLo2 + x.aHi + x.bHi + x.oldHi
  else x.carryLo + x.aHi + x.bHi + x.immHi
def carryHi (x : Arith) : Nat :=
  if x.sel = 1 then (if x.aHi < x.bHi + x.carryLo then 1 else 0)
  else if x.sel = 3 then (if 65536 ≤ x.sumHi then 1 else 0) else x.sumHi / 65536
def carryHi2 (x : Arith) : Nat := if x.sel = 3 ∧ 131072 ≤ x.sumHi then 1 else 0
def outHi (x : Arith) : Nat :=
  if x.sel = 1 then x.aHi + 65536 * x.carryHi - x.bHi - x.carryLo else x.sumHi % 65536

/-- Range conditions of an honest additive row; the ordering of previous port accesses
    is a separate `Frame.Valid` premise, needed only for the timestamp queries. -/
structure Valid (x : Arith) : Prop where
  clock : x.frame.Clock
  sel : x.sel ≤ 3
  rs2 : x.rs2 < 65536
  rd : x.rd < 65536
  aLo : x.aLo < 65536
  aHi : x.aHi < 65536
  bLo : x.bLo < 65536
  bHi : x.bHi < 65536
  oldLo : x.oldLo < 65536
  oldHi : x.oldHi < 65536
  carryLo : x.carryLo ≤ 1
  carryHi : x.carryHi ≤ 1

/-- The honest witness columns of an additive row. Column 20 is the complement of the
    other three selectors so the selector sum is `1` by `ring`. -/
def honest (x : Arith) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 => 1
  | 5 => (x.rs1 : Nat)
  | 6 | 38 => (x.rs2 : Nat)
  | 7 | 44 => (x.rd : Nat)
  | 8 => (x.immLo : Nat) | 9 => (x.immHi : Nat)
  | 11 => (x.isSel 0 : Nat) | 12 => (x.isSel 1 : Nat) | 13 => (x.isSel 2 : Nat)
  | 20 => 1 - (x.isSel 0 : Nat) - (x.isSel 1 : Nat) - (x.isSel 2 : Nat)
  | 30 => (x.frame.finalPcLo : Nat) | 31 => (x.frame.finalPcHi : Nat)
  | 32 => (x.frame.finalTsLo : Nat) | 33 => (x.frame.finalTsHi : Nat)
  | 34 => (x.frame.prev0Lo : Nat) | 35 => (x.frame.prev0Hi : Nat)
  | 40 => (x.frame.prev1Lo : Nat) | 41 => (x.frame.prev1Hi : Nat)
  | 46 => (x.frame.prev2Lo : Nat) | 47 => (x.frame.prev2Hi : Nat)
  | 36 => (x.aLo : Nat) | 37 => (x.aHi : Nat)
  | 42 => (x.bLo : Nat) | 43 => (x.bHi : Nat)
  | 48 => (x.oldLo : Nat) | 49 => (x.oldHi : Nat)
  | 50 => (x.outLo : Nat) | 51 => (x.outHi : Nat)
  | 52 => (x.carryHi : Nat) | 53 => (x.carryLo : Nat)
  | 54 => (x.carryLo2 : Nat) | 55 => (x.carryHi2 : Nat)
  | 78 => ((x.aLo : Nat) + 65536 * (x.aHi : Nat)) * ((x.bLo : Nat) + 65536 * (x.bHi : Nat)) * 943718400
  | 122 => (x.frame.pcCarry : Nat)
  | 123 => (x.frame.borrow0 : Nat) | 124 => (x.frame.borrow1 : Nat)
  | 125 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[unified_honest] theorem col_0 (x : Arith) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_1 (x : Arith) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_2 (x : Arith) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_3 (x : Arith) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_4 (x : Arith) : x.honest 4 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_5 (x : Arith) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_6 (x : Arith) : x.honest 6 = ((x.rs2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_7 (x : Arith) : x.honest 7 = ((x.rd : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_8 (x : Arith) : x.honest 8 = ((x.immLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_9 (x : Arith) : x.honest 9 = ((x.immHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_10 (x : Arith) : x.honest 10 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_11 (x : Arith) : x.honest 11 = ((x.isSel 0 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_12 (x : Arith) : x.honest 12 = ((x.isSel 1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_13 (x : Arith) : x.honest 13 = ((x.isSel 2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_14 (x : Arith) : x.honest 14 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_15 (x : Arith) : x.honest 15 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_16 (x : Arith) : x.honest 16 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_17 (x : Arith) : x.honest 17 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_18 (x : Arith) : x.honest 18 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_19 (x : Arith) : x.honest 19 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_20 (x : Arith) : x.honest 20 = (1 - (x.isSel 0 : Nat) - (x.isSel 1 : Nat) - (x.isSel 2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_21 (x : Arith) : x.honest 21 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_22 (x : Arith) : x.honest 22 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_23 (x : Arith) : x.honest 23 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_24 (x : Arith) : x.honest 24 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_25 (x : Arith) : x.honest 25 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_26 (x : Arith) : x.honest 26 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_27 (x : Arith) : x.honest 27 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_28 (x : Arith) : x.honest 28 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_29 (x : Arith) : x.honest 29 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_30 (x : Arith) : x.honest 30 = ((x.frame.finalPcLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_31 (x : Arith) : x.honest 31 = ((x.frame.finalPcHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_32 (x : Arith) : x.honest 32 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_33 (x : Arith) : x.honest 33 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_34 (x : Arith) : x.honest 34 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_35 (x : Arith) : x.honest 35 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_36 (x : Arith) : x.honest 36 = ((x.aLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_37 (x : Arith) : x.honest 37 = ((x.aHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_38 (x : Arith) : x.honest 38 = ((x.rs2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_39 (x : Arith) : x.honest 39 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_40 (x : Arith) : x.honest 40 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_41 (x : Arith) : x.honest 41 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_42 (x : Arith) : x.honest 42 = ((x.bLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_43 (x : Arith) : x.honest 43 = ((x.bHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_44 (x : Arith) : x.honest 44 = ((x.rd : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_45 (x : Arith) : x.honest 45 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_46 (x : Arith) : x.honest 46 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_47 (x : Arith) : x.honest 47 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_48 (x : Arith) : x.honest 48 = ((x.oldLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_49 (x : Arith) : x.honest 49 = ((x.oldHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_50 (x : Arith) : x.honest 50 = ((x.outLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_51 (x : Arith) : x.honest 51 = ((x.outHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_52 (x : Arith) : x.honest 52 = ((x.carryHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_53 (x : Arith) : x.honest 53 = ((x.carryLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_54 (x : Arith) : x.honest 54 = ((x.carryLo2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_55 (x : Arith) : x.honest 55 = ((x.carryHi2 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_56 (x : Arith) : x.honest 56 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_57 (x : Arith) : x.honest 57 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_58 (x : Arith) : x.honest 58 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_59 (x : Arith) : x.honest 59 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_60 (x : Arith) : x.honest 60 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_61 (x : Arith) : x.honest 61 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_62 (x : Arith) : x.honest 62 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_63 (x : Arith) : x.honest 63 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_64 (x : Arith) : x.honest 64 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_65 (x : Arith) : x.honest 65 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_66 (x : Arith) : x.honest 66 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_67 (x : Arith) : x.honest 67 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_68 (x : Arith) : x.honest 68 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_69 (x : Arith) : x.honest 69 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_70 (x : Arith) : x.honest 70 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_71 (x : Arith) : x.honest 71 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_72 (x : Arith) : x.honest 72 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_73 (x : Arith) : x.honest 73 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_74 (x : Arith) : x.honest 74 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_75 (x : Arith) : x.honest 75 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_76 (x : Arith) : x.honest 76 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_77 (x : Arith) : x.honest 77 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_78 (x : Arith) : x.honest 78 = (((x.aLo : Nat) + 65536 * (x.aHi : Nat)) * ((x.bLo : Nat) + 65536 * (x.bHi : Nat)) * 943718400 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_79 (x : Arith) : x.honest 79 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_80 (x : Arith) : x.honest 80 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_81 (x : Arith) : x.honest 81 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_82 (x : Arith) : x.honest 82 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_83 (x : Arith) : x.honest 83 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_84 (x : Arith) : x.honest 84 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_85 (x : Arith) : x.honest 85 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_86 (x : Arith) : x.honest 86 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_87 (x : Arith) : x.honest 87 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_88 (x : Arith) : x.honest 88 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_89 (x : Arith) : x.honest 89 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_90 (x : Arith) : x.honest 90 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_91 (x : Arith) : x.honest 91 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_92 (x : Arith) : x.honest 92 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_93 (x : Arith) : x.honest 93 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_94 (x : Arith) : x.honest 94 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_95 (x : Arith) : x.honest 95 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_96 (x : Arith) : x.honest 96 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_97 (x : Arith) : x.honest 97 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_98 (x : Arith) : x.honest 98 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_99 (x : Arith) : x.honest 99 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_100 (x : Arith) : x.honest 100 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_101 (x : Arith) : x.honest 101 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_102 (x : Arith) : x.honest 102 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_103 (x : Arith) : x.honest 103 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_104 (x : Arith) : x.honest 104 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_105 (x : Arith) : x.honest 105 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_106 (x : Arith) : x.honest 106 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_107 (x : Arith) : x.honest 107 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_108 (x : Arith) : x.honest 108 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_109 (x : Arith) : x.honest 109 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_110 (x : Arith) : x.honest 110 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_111 (x : Arith) : x.honest 111 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_112 (x : Arith) : x.honest 112 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_113 (x : Arith) : x.honest 113 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_114 (x : Arith) : x.honest 114 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_115 (x : Arith) : x.honest 115 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_116 (x : Arith) : x.honest 116 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_117 (x : Arith) : x.honest 117 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_118 (x : Arith) : x.honest 118 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_119 (x : Arith) : x.honest 119 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_120 (x : Arith) : x.honest 120 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_121 (x : Arith) : x.honest 121 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_122 (x : Arith) : x.honest 122 = ((x.frame.pcCarry : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_123 (x : Arith) : x.honest 123 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_124 (x : Arith) : x.honest 124 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_125 (x : Arith) : x.honest 125 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := by rfl
-- END generated columns

theorem columns (x : Arith) : x.frame.Columns x.honest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem cast_mod (n d : Nat) :
    ((n % d : Nat) : ZMod babyBearModulus) =
      (n : ZMod babyBearModulus) - (d : Nat) * ((n / d : Nat) : ZMod babyBearModulus) := by
  have h := congrArg (Nat.cast : Nat → ZMod babyBearModulus) (Nat.mod_add_div n d)
  push_cast at h ⊢
  linear_combination h

private theorem bool_of_le {n : Nat} (h : n ≤ 1) :
    (n : ZMod babyBearModulus) * ((n : ZMod babyBearModulus) - 1) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> simp

theorem carryLo2_le (x : Arith) : x.carryLo2 ≤ 1 := by unfold carryLo2; split <;> omega
theorem carryHi2_le (x : Arith) : x.carryHi2 ≤ 1 := by unfold carryHi2; split <;> omega

theorem outLo_lt {x : Arith} (hx : x.Valid) : x.outLo < 65536 := by
  have := hx.aLo; have := hx.bLo
  unfold outLo carryLo; split
  · split <;> omega
  · exact Nat.mod_lt _ (by decide)

theorem outHi_lt {x : Arith} (hx : x.Valid) : x.outHi < 65536 := by
  have := hx.aHi; have := hx.bHi; have := hx.carryLo
  unfold outHi carryHi; split
  · split <;> omega
  · exact Nat.mod_lt _ (by decide)

/-- Low-limb equation per selector, as the circuit states it. -/
theorem low (x : Arith) (hx : x.Valid) :
    (x.isSel 0 : ZMod babyBearModulus) * ((x.aLo : Nat) + (x.bLo : Nat) + (x.immLo : Nat) - (x.outLo : Nat) -
        65536 * (x.carryLo : Nat)) +
      (x.isSel 2 : Nat) * ((x.frame.pcLo : Nat) + (x.immLo : Nat) - (x.outLo : Nat) - 65536 * (x.carryLo : Nat)) +
      (x.isSel 1 : Nat) * ((x.outLo : Nat) + (x.bLo : Nat) - (x.aLo : Nat) - 65536 * (x.carryLo : Nat)) +
      (1 - (x.isSel 0 : Nat) - (x.isSel 1 : Nat) - (x.isSel 2 : Nat)) *
        ((x.aLo : Nat) + (x.bLo : Nat) + (x.oldLo : Nat) - (x.outLo : Nat) -
          65536 * ((x.carryLo : Nat) + (x.carryLo2 : Nat))) = 0 := by
  have := hx.aLo; have := hx.bLo; have := hx.oldLo; have hs := hx.sel; have hc := hx.carryLo
  obtain h | h | h | h : x.sel = 0 ∨ x.sel = 1 ∨ x.sel = 2 ∨ x.sel = 3 := by omega
  all_goals simp only [isSel, h, Nat.reduceEqDiff, ↓reduceIte, Nat.cast_one, Nat.cast_zero,
    zero_mul, one_mul, add_zero, zero_add, sub_zero, sub_self]
  · have e := cast_mod x.sumLo 65536
    simp only [outLo, carryLo, sumLo, h, Nat.reduceEqDiff, ↓reduceIte] at e ⊢
    push_cast at e ⊢; linear_combination -e
  · simp only [outLo, carryLo, h, ↓reduceIte] at hc ⊢
    split <;> (rw [Nat.cast_sub (by omega)]; push_cast; ring)
  · have e := cast_mod x.sumLo 65536
    simp only [outLo, carryLo, sumLo, h, Nat.reduceEqDiff, ↓reduceIte] at e ⊢
    push_cast at e ⊢; linear_combination -e
  · have hlt : x.sumLo < 196608 := by simp only [sumLo, h, Nat.reduceEqDiff, ↓reduceIte]; omega
    have e : x.sumLo = x.outLo + 65536 * (x.carryLo + x.carryLo2) := by
      simp only [outLo, carryLo, carryLo2, h, Nat.reduceEqDiff, ↓reduceIte, true_and]
      split <;> split <;> omega
    have e' := congrArg (Nat.cast : Nat → ZMod babyBearModulus) e
    simp only [sumLo, h, Nat.reduceEqDiff, ↓reduceIte] at e'
    push_cast at e' ⊢; linear_combination e'

/-- High-limb equation per selector, as the circuit states it. -/
theorem high (x : Arith) (hx : x.Valid) :
    (x.isSel 0 : ZMod babyBearModulus) * ((x.carryLo : Nat) + (x.aHi : Nat) + (x.bHi : Nat) + (x.immHi : Nat) -
        (x.outHi : Nat) - 65536 * (x.carryHi : Nat)) +
      (x.isSel 2 : Nat) * ((x.carryLo : Nat) + (x.frame.pcHi : Nat) + (x.immHi : Nat) - (x.outHi : Nat) -
        65536 * (x.carryHi : Nat)) +
      (x.isSel 1 : Nat) * ((x.carryLo : Nat) + (x.outHi : Nat) + (x.bHi : Nat) - (x.aHi : Nat) -
        65536 * (x.carryHi : Nat)) +
      (1 - (x.isSel 0 : Nat) - (x.isSel 1 : Nat) - (x.isSel 2 : Nat)) *
        ((x.carryLo : Nat) + (x.carryLo2 : Nat) + (x.aHi : Nat) + (x.bHi : Nat) + (x.oldHi : Nat) -
          (x.outHi : Nat) - 65536 * ((x.carryHi : Nat) + (x.carryHi2 : Nat))) = 0 := by
  have := hx.aHi; have := hx.bHi; have := hx.oldHi; have hs := hx.sel; have hc := hx.carryHi
  have hcl := hx.carryLo; have := x.carryLo2_le
  obtain h | h | h | h : x.sel = 0 ∨ x.sel = 1 ∨ x.sel = 2 ∨ x.sel = 3 := by omega
  all_goals simp only [isSel, h, Nat.reduceEqDiff, ↓reduceIte, Nat.cast_one, Nat.cast_zero,
    zero_mul, one_mul, add_zero, zero_add, sub_zero, sub_self]
  · have e := cast_mod x.sumHi 65536
    simp only [outHi, carryHi, sumHi, h, Nat.reduceEqDiff, ↓reduceIte] at e ⊢
    push_cast at e ⊢; linear_combination -e
  · simp only [outHi, carryHi, h, ↓reduceIte] at hc ⊢
    split <;> (rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring)
  · have e := cast_mod x.sumHi 65536
    simp only [outHi, carryHi, sumHi, h, Nat.reduceEqDiff, ↓reduceIte] at e ⊢
    push_cast at e ⊢; linear_combination -e
  · have hlt : x.sumHi < 196608 := by simp only [sumHi, h, Nat.reduceEqDiff, ↓reduceIte]; omega
    have e : x.sumHi = x.outHi + 65536 * (x.carryHi + x.carryHi2) := by
      simp only [outHi, carryHi, carryHi2, h, Nat.reduceEqDiff, ↓reduceIte, true_and]
      split <;> split <;> omega
    have e' := congrArg (Nat.cast : Nat → ZMod babyBearModulus) e
    simp only [sumHi, h, Nat.reduceEqDiff, ↓reduceIte] at e'
    push_cast at e' ⊢; linear_combination e'

theorem complete_core (x : Arith) (hx : x.Valid) (t : Table (ZMod babyBearModulus) (fields 10))
    (zero : ZeroRow t) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (importedConstraints t) := by
  have hf := hx.clock
  have := hx.rs2; have := hx.rd; have := hf.pcHi
  have : x.frame.pcHi < 65536 := by have := hf.pcHi; unfold Frame.finalPcHi at this; omega
  have : x.frame.finalPcLo < 65536 := Nat.mod_lt _ (by decide)
  have := outLo_lt hx; have := outHi_lt hx
  have hcl := hx.carryLo; have hch := hx.carryHi
  have hcl2 := x.carryLo2_le; have hch2 := x.carryHi2_le
  have hl := low x hx; have hh := high x hx
  simp only [importedConstraints, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  -- goals 1-120: equations; 121-133: 16-bit ranges; 134-138: setup lookups
  iterate 5
    on_goal 134 =>
      refine zero _ _ ?_
      apply Vector.ext
      intro j hj
      interval_cases j <;> simp [Expression.eval, environment, unified_honest]
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
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul,
    add_zero, zero_add, mul_one, one_mul]
  all_goals first
    | ring1
    | linear_combination x.frame.pc_low
    | linear_combination -x.frame.pc_high
    | linear_combination x.frame.ts_square hf
    | linear_combination x.frame.ts_high
    | linear_combination Frame.pcCarry_bool hf
    | linear_combination x.frame.borrow0_bool
    | linear_combination x.frame.borrow1_bool
    | linear_combination x.frame.borrow2_bool
    | linear_combination bool_of_le hcl
    | linear_combination bool_of_le hch
    | linear_combination bool_of_le hcl2
    | linear_combination bool_of_le hch2
    | linear_combination hl
    | linear_combination hh
    | (have hs := hx.sel
       obtain h | h | h | h : x.sel = 0 ∨ x.sel = 1 ∨ x.sel = 2 ∨ x.sel = 3 := by omega
       all_goals simp only [isSel, h, Nat.reduceEqDiff, ↓reduceIte, Nat.cast_one, Nat.cast_zero]
       all_goals ring1)

theorem complete (x : Arith) (hx : x.Valid) (hf : x.frame.Valid)
    (t : Table (ZMod babyBearModulus) (fields 10)) (zero : ZeroRow t) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (clockConstraints t) :=
  holds_append (complete_core x hx t zero) (Frame.timestamps hf x.columns)

end Arith

end Airbender.UnifiedReduced.Completeness
