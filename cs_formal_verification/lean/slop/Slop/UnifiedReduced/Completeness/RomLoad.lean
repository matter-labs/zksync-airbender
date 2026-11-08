module
public import Slop.UnifiedReduced.Completeness.Arith

@[expose] public section

/-! Completeness of the unified circuit for its ROM word loads (LW inside the ROM window):
    the honest assignment, whose loaded word is the public ROM word at the address, satisfies
    every equation, range query and setup lookup of the unified setup table. Proved once,
    symbolically. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true
set_option maxRecDepth 16384

/-- Inputs of one honest ROM word load. `base*` is the base register's value, `imm*` the
    offset limbs, `val*` the loaded ROM word, `shadow*` the RAM port's (ignored) read value
    and `old*` the destination's previous value. -/
structure RomLoad where
  frame : Frame
  rs1 : Nat
  rd : Nat
  baseLo : Nat
  baseHi : Nat
  immLo : Nat
  immHi : Nat
  valLo : Nat
  valHi : Nat
  shadowLo : Nat
  shadowHi : Nat
  oldLo : Nat
  oldHi : Nat

namespace RomLoad

def sumLo (x : RomLoad) : Nat := x.baseLo + x.immLo
def carryLo (x : RomLoad) : Nat := x.sumLo / 65536
def addrLo (x : RomLoad) : Nat := x.sumLo % 65536
def sumHi (x : RomLoad) : Nat := x.baseHi + x.immHi + x.carryLo
def carryHi (x : RomLoad) : Nat := x.sumHi / 65536
def addrHi (x : RomLoad) : Nat := x.sumHi % 65536
/-- The ROM word index of the address. -/
def key (x : RomLoad) : Nat := (x.addrLo + 65536 * x.addrHi) / 4

/-- Range conditions of an honest ROM load: limbs in range, a word-aligned address inside the
    ROM window (high limb below 64). The loaded word is a separate premise of `complete`. -/
structure Valid (x : RomLoad) : Prop where
  clock : x.frame.Clock
  rd : x.rd < 65536
  baseLo : x.baseLo < 65536
  baseHi : x.baseHi < 65536
  immLo : x.immLo < 65536
  immHi : x.immHi < 65536
  valLo : x.valLo < 65536
  valHi : x.valHi < 65536
  aligned : x.addrLo % 4 = 0
  rom : x.addrHi < 64

/-- The honest witness columns of a ROM word load. -/
def honest (x : RomLoad) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 | 28 | 54 | 81 => 1
  | 5 => (x.rs1 : Nat)
  | 7 | 44 => (x.rd : Nat)
  | 8 => (x.immLo : Nat) | 9 => (x.immHi : Nat)
  | 30 => (x.frame.finalPcLo : Nat) | 31 => (x.frame.finalPcHi : Nat)
  | 32 => (x.frame.finalTsLo : Nat) | 33 => (x.frame.finalTsHi : Nat)
  | 34 => (x.frame.prev0Lo : Nat) | 35 => (x.frame.prev0Hi : Nat)
  | 40 => (x.frame.prev1Lo : Nat) | 41 => (x.frame.prev1Hi : Nat)
  | 46 => (x.frame.prev2Lo : Nat) | 47 => (x.frame.prev2Hi : Nat)
  | 36 => (x.baseLo : Nat) | 37 => (x.baseHi : Nat)
  | 38 | 57 => (x.addrLo : Nat) | 39 | 58 => (x.addrHi : Nat)
  | 42 => (x.shadowLo : Nat) | 43 => (x.shadowHi : Nat)
  | 48 => (x.oldLo : Nat) | 49 => (x.oldHi : Nat)
  | 50 | 84 => (x.valLo : Nat) | 51 | 85 => (x.valHi : Nat)
  | 52 => (x.carryLo : Nat) | 53 => (x.carryHi : Nat)
  | 74 => (x.addrLo / 4 : Nat)
  | 78 => ((x.baseLo : Nat) + 65536 * (x.baseHi : Nat)) * ((x.shadowLo : Nat) + 65536 * (x.shadowHi : Nat)) *
      943718400
  | 80 => (65472 + x.addrHi : Nat)
  | 82 => 34
  | 83 => (x.addrLo + 65536 * x.addrHi : Nat)
  | 122 => (x.frame.pcCarry : Nat)
  | 123 => (x.frame.borrow0 : Nat) | 124 => (x.frame.borrow1 : Nat)
  | 125 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[unified_honest] theorem col_0 (x : RomLoad) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_1 (x : RomLoad) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_2 (x : RomLoad) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_3 (x : RomLoad) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_4 (x : RomLoad) : x.honest 4 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_5 (x : RomLoad) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_6 (x : RomLoad) : x.honest 6 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_7 (x : RomLoad) : x.honest 7 = ((x.rd : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_8 (x : RomLoad) : x.honest 8 = ((x.immLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_9 (x : RomLoad) : x.honest 9 = ((x.immHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_10 (x : RomLoad) : x.honest 10 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_11 (x : RomLoad) : x.honest 11 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_12 (x : RomLoad) : x.honest 12 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_13 (x : RomLoad) : x.honest 13 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_14 (x : RomLoad) : x.honest 14 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_15 (x : RomLoad) : x.honest 15 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_16 (x : RomLoad) : x.honest 16 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_17 (x : RomLoad) : x.honest 17 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_18 (x : RomLoad) : x.honest 18 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_19 (x : RomLoad) : x.honest 19 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_20 (x : RomLoad) : x.honest 20 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_21 (x : RomLoad) : x.honest 21 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_22 (x : RomLoad) : x.honest 22 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_23 (x : RomLoad) : x.honest 23 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_24 (x : RomLoad) : x.honest 24 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_25 (x : RomLoad) : x.honest 25 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_26 (x : RomLoad) : x.honest 26 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_27 (x : RomLoad) : x.honest 27 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_28 (x : RomLoad) : x.honest 28 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_29 (x : RomLoad) : x.honest 29 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_30 (x : RomLoad) : x.honest 30 = ((x.frame.finalPcLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_31 (x : RomLoad) : x.honest 31 = ((x.frame.finalPcHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_32 (x : RomLoad) : x.honest 32 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_33 (x : RomLoad) : x.honest 33 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_34 (x : RomLoad) : x.honest 34 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_35 (x : RomLoad) : x.honest 35 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_36 (x : RomLoad) : x.honest 36 = ((x.baseLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_37 (x : RomLoad) : x.honest 37 = ((x.baseHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_38 (x : RomLoad) : x.honest 38 = ((x.addrLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_39 (x : RomLoad) : x.honest 39 = ((x.addrHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_40 (x : RomLoad) : x.honest 40 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_41 (x : RomLoad) : x.honest 41 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_42 (x : RomLoad) : x.honest 42 = ((x.shadowLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_43 (x : RomLoad) : x.honest 43 = ((x.shadowHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_44 (x : RomLoad) : x.honest 44 = ((x.rd : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_45 (x : RomLoad) : x.honest 45 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_46 (x : RomLoad) : x.honest 46 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_47 (x : RomLoad) : x.honest 47 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_48 (x : RomLoad) : x.honest 48 = ((x.oldLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_49 (x : RomLoad) : x.honest 49 = ((x.oldHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_50 (x : RomLoad) : x.honest 50 = ((x.valLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_51 (x : RomLoad) : x.honest 51 = ((x.valHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_52 (x : RomLoad) : x.honest 52 = ((x.carryLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_53 (x : RomLoad) : x.honest 53 = ((x.carryHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_54 (x : RomLoad) : x.honest 54 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_55 (x : RomLoad) : x.honest 55 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_56 (x : RomLoad) : x.honest 56 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_57 (x : RomLoad) : x.honest 57 = ((x.addrLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_58 (x : RomLoad) : x.honest 58 = ((x.addrHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_59 (x : RomLoad) : x.honest 59 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_60 (x : RomLoad) : x.honest 60 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_61 (x : RomLoad) : x.honest 61 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_62 (x : RomLoad) : x.honest 62 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_63 (x : RomLoad) : x.honest 63 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_64 (x : RomLoad) : x.honest 64 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_65 (x : RomLoad) : x.honest 65 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_66 (x : RomLoad) : x.honest 66 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_67 (x : RomLoad) : x.honest 67 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_68 (x : RomLoad) : x.honest 68 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_69 (x : RomLoad) : x.honest 69 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_70 (x : RomLoad) : x.honest 70 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_71 (x : RomLoad) : x.honest 71 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_72 (x : RomLoad) : x.honest 72 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_73 (x : RomLoad) : x.honest 73 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_74 (x : RomLoad) : x.honest 74 = ((x.addrLo / 4 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_75 (x : RomLoad) : x.honest 75 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_76 (x : RomLoad) : x.honest 76 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_77 (x : RomLoad) : x.honest 77 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_78 (x : RomLoad) : x.honest 78 = (((x.baseLo : Nat) + 65536 * (x.baseHi : Nat)) * ((x.shadowLo : Nat) + 65536 * (x.shadowHi : Nat)) * 943718400 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_79 (x : RomLoad) : x.honest 79 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_80 (x : RomLoad) : x.honest 80 = ((65472 + x.addrHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_81 (x : RomLoad) : x.honest 81 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_82 (x : RomLoad) : x.honest 82 = (34 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_83 (x : RomLoad) : x.honest 83 = ((x.addrLo + 65536 * x.addrHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_84 (x : RomLoad) : x.honest 84 = ((x.valLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_85 (x : RomLoad) : x.honest 85 = ((x.valHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_86 (x : RomLoad) : x.honest 86 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_87 (x : RomLoad) : x.honest 87 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_88 (x : RomLoad) : x.honest 88 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_89 (x : RomLoad) : x.honest 89 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_90 (x : RomLoad) : x.honest 90 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_91 (x : RomLoad) : x.honest 91 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_92 (x : RomLoad) : x.honest 92 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_93 (x : RomLoad) : x.honest 93 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_94 (x : RomLoad) : x.honest 94 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_95 (x : RomLoad) : x.honest 95 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_96 (x : RomLoad) : x.honest 96 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_97 (x : RomLoad) : x.honest 97 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_98 (x : RomLoad) : x.honest 98 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_99 (x : RomLoad) : x.honest 99 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_100 (x : RomLoad) : x.honest 100 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_101 (x : RomLoad) : x.honest 101 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_102 (x : RomLoad) : x.honest 102 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_103 (x : RomLoad) : x.honest 103 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_104 (x : RomLoad) : x.honest 104 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_105 (x : RomLoad) : x.honest 105 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_106 (x : RomLoad) : x.honest 106 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_107 (x : RomLoad) : x.honest 107 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_108 (x : RomLoad) : x.honest 108 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_109 (x : RomLoad) : x.honest 109 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_110 (x : RomLoad) : x.honest 110 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_111 (x : RomLoad) : x.honest 111 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_112 (x : RomLoad) : x.honest 112 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_113 (x : RomLoad) : x.honest 113 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_114 (x : RomLoad) : x.honest 114 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_115 (x : RomLoad) : x.honest 115 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_116 (x : RomLoad) : x.honest 116 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_117 (x : RomLoad) : x.honest 117 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_118 (x : RomLoad) : x.honest 118 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_119 (x : RomLoad) : x.honest 119 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_120 (x : RomLoad) : x.honest 120 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_121 (x : RomLoad) : x.honest 121 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_122 (x : RomLoad) : x.honest 122 = ((x.frame.pcCarry : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_123 (x : RomLoad) : x.honest 123 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_124 (x : RomLoad) : x.honest 124 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_125 (x : RomLoad) : x.honest 125 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := by rfl
-- END generated columns

theorem columns (x : RomLoad) : x.frame.Columns x.honest :=
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

theorem low (x : RomLoad) :
    (x.baseLo : ZMod babyBearModulus) + (x.immLo : Nat) - (x.addrLo : Nat) - 65536 * (x.carryLo : Nat) = 0 := by
  have e := cast_mod x.sumLo 65536
  simp only [addrLo, carryLo, sumLo] at e ⊢
  push_cast at e ⊢; linear_combination -e

theorem high (x : RomLoad) :
    (x.baseHi : ZMod babyBearModulus) + (x.immHi : Nat) + (x.carryLo : Nat) - (x.addrHi : Nat) -
      65536 * (x.carryHi : Nat) = 0 := by
  have e := cast_mod x.sumHi 65536
  simp only [addrHi, carryHi, sumHi] at e ⊢
  push_cast at e ⊢; linear_combination -e

theorem align {x : RomLoad} (hx : x.Valid) :
    4 * ((x.addrLo / 4 : Nat) : ZMod babyBearModulus) - (x.addrLo : Nat) = 0 := by
  have e : 4 * (x.addrLo / 4) = x.addrLo := by have := hx.aligned; omega
  have e' := congrArg (Nat.cast : Nat → ZMod babyBearModulus) e
  push_cast at e'; linear_combination e'

end RomLoad

end Airbender.UnifiedReduced.Completeness
