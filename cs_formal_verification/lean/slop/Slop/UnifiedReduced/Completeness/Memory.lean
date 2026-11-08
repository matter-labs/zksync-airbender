module
public import Slop.UnifiedReduced.Completeness.Arith

@[expose] public section

/-! Completeness of the unified circuit for its RAM word accesses (LW/SW outside the
    ROM window): the honest assignment satisfies every equation, range query and
    (disabled) setup lookup, for any setup table holding the all-zero query. Proved
    once, symbolically; only the load/store case is split. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true
set_option maxRecDepth 16384

/-- Inputs of one honest RAM word access. `reg` is the destination (load) or source
    (store) register index; `base*` is the base register's value, `imm*` the offset limbs,
    `val*` the word loaded or stored, `old*` the value the written port held before. -/
structure Memory where
  frame : Frame
  store : Bool
  rs1 : Nat
  reg : Nat
  baseLo : Nat
  baseHi : Nat
  immLo : Nat
  immHi : Nat
  valLo : Nat
  valHi : Nat
  oldLo : Nat
  oldHi : Nat

namespace Memory

def sumLo (x : Memory) : Nat := x.baseLo + x.immLo
def carryLo (x : Memory) : Nat := x.sumLo / 65536
def addrLo (x : Memory) : Nat := x.sumLo % 65536
def sumHi (x : Memory) : Nat := x.baseHi + x.immHi + x.carryLo
def carryHi (x : Memory) : Nat := x.sumHi / 65536
def addrHi (x : Memory) : Nat := x.sumHi % 65536

/-- Range conditions of an honest RAM access: limbs in range, a word-aligned address,
    and an address outside the ROM window (high limb at least 64). The ordering of
    previous port accesses is a separate `Frame.Valid` premise. -/
structure Valid (x : Memory) : Prop where
  clock : x.frame.Clock
  reg : x.reg < 65536
  baseLo : x.baseLo < 65536
  baseHi : x.baseHi < 65536
  immLo : x.immLo < 65536
  immHi : x.immHi < 65536
  valLo : x.valLo < 65536
  valHi : x.valHi < 65536
  aligned : x.addrLo % 4 = 0
  ram : 64 ≤ x.addrHi

/-- The honest witness columns of a RAM word access: the memory word goes through the
    first port for a load (address in 38/39) and the second port for a store (44/45). -/
def honest (x : Memory) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 => 1
  | 5 => (x.rs1 : Nat)
  | 6 => if x.store then (x.reg : Nat) else 0
  | 7 => if x.store then 0 else (x.reg : Nat)
  | 8 => (x.immLo : Nat) | 9 => (x.immHi : Nat)
  | 28 => if x.store then 0 else 1
  | 29 => if x.store then 1 else 0
  | 30 => (x.frame.finalPcLo : Nat) | 31 => (x.frame.finalPcHi : Nat)
  | 32 => (x.frame.finalTsLo : Nat) | 33 => (x.frame.finalTsHi : Nat)
  | 34 => (x.frame.prev0Lo : Nat) | 35 => (x.frame.prev0Hi : Nat)
  | 40 => (x.frame.prev1Lo : Nat) | 41 => (x.frame.prev1Hi : Nat)
  | 46 => (x.frame.prev2Lo : Nat) | 47 => (x.frame.prev2Hi : Nat)
  | 36 => (x.baseLo : Nat) | 37 => (x.baseHi : Nat)
  | 38 => if x.store then (x.reg : Nat) else (x.addrLo : Nat)
  | 39 => if x.store then 0 else (x.addrHi : Nat)
  | 44 => if x.store then (x.addrLo : Nat) else (x.reg : Nat)
  | 45 => if x.store then (x.addrHi : Nat) else 0
  | 42 | 50 => (x.valLo : Nat) | 43 | 51 => (x.valHi : Nat)
  | 48 => (x.oldLo : Nat) | 49 => (x.oldHi : Nat)
  | 52 => (x.carryLo : Nat) | 53 => (x.carryHi : Nat)
  | 57 => (x.addrLo : Nat) | 58 => (x.addrHi : Nat)
  | 74 => (x.addrLo / 4 : Nat)
  | 78 => ((x.baseLo : Nat) + 65536 * (x.baseHi : Nat)) * ((x.valLo : Nat) + 65536 * (x.valHi : Nat)) * 943718400
  | 80 => (x.addrHi - 64 : Nat)
  | 122 => (x.frame.pcCarry : Nat)
  | 123 => (x.frame.borrow0 : Nat) | 124 => (x.frame.borrow1 : Nat)
  | 125 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[unified_honest] theorem col_0 (x : Memory) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_1 (x : Memory) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_2 (x : Memory) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_3 (x : Memory) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_4 (x : Memory) : x.honest 4 = (1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_5 (x : Memory) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_6 (x : Memory) : x.honest 6 = (if x.store then (x.reg : Nat) else 0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_7 (x : Memory) : x.honest 7 = (if x.store then 0 else (x.reg : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_8 (x : Memory) : x.honest 8 = ((x.immLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_9 (x : Memory) : x.honest 9 = ((x.immHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_10 (x : Memory) : x.honest 10 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_11 (x : Memory) : x.honest 11 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_12 (x : Memory) : x.honest 12 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_13 (x : Memory) : x.honest 13 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_14 (x : Memory) : x.honest 14 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_15 (x : Memory) : x.honest 15 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_16 (x : Memory) : x.honest 16 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_17 (x : Memory) : x.honest 17 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_18 (x : Memory) : x.honest 18 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_19 (x : Memory) : x.honest 19 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_20 (x : Memory) : x.honest 20 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_21 (x : Memory) : x.honest 21 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_22 (x : Memory) : x.honest 22 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_23 (x : Memory) : x.honest 23 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_24 (x : Memory) : x.honest 24 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_25 (x : Memory) : x.honest 25 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_26 (x : Memory) : x.honest 26 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_27 (x : Memory) : x.honest 27 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_28 (x : Memory) : x.honest 28 = (if x.store then 0 else 1 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_29 (x : Memory) : x.honest 29 = (if x.store then 1 else 0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_30 (x : Memory) : x.honest 30 = ((x.frame.finalPcLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_31 (x : Memory) : x.honest 31 = ((x.frame.finalPcHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_32 (x : Memory) : x.honest 32 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_33 (x : Memory) : x.honest 33 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_34 (x : Memory) : x.honest 34 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_35 (x : Memory) : x.honest 35 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_36 (x : Memory) : x.honest 36 = ((x.baseLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_37 (x : Memory) : x.honest 37 = ((x.baseHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_38 (x : Memory) : x.honest 38 = (if x.store then (x.reg : Nat) else (x.addrLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_39 (x : Memory) : x.honest 39 = (if x.store then 0 else (x.addrHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_40 (x : Memory) : x.honest 40 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_41 (x : Memory) : x.honest 41 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_42 (x : Memory) : x.honest 42 = ((x.valLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_43 (x : Memory) : x.honest 43 = ((x.valHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_44 (x : Memory) : x.honest 44 = (if x.store then (x.addrLo : Nat) else (x.reg : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_45 (x : Memory) : x.honest 45 = (if x.store then (x.addrHi : Nat) else 0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_46 (x : Memory) : x.honest 46 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_47 (x : Memory) : x.honest 47 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_48 (x : Memory) : x.honest 48 = ((x.oldLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_49 (x : Memory) : x.honest 49 = ((x.oldHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_50 (x : Memory) : x.honest 50 = ((x.valLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_51 (x : Memory) : x.honest 51 = ((x.valHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_52 (x : Memory) : x.honest 52 = ((x.carryLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_53 (x : Memory) : x.honest 53 = ((x.carryHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_54 (x : Memory) : x.honest 54 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_55 (x : Memory) : x.honest 55 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_56 (x : Memory) : x.honest 56 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_57 (x : Memory) : x.honest 57 = ((x.addrLo : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_58 (x : Memory) : x.honest 58 = ((x.addrHi : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_59 (x : Memory) : x.honest 59 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_60 (x : Memory) : x.honest 60 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_61 (x : Memory) : x.honest 61 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_62 (x : Memory) : x.honest 62 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_63 (x : Memory) : x.honest 63 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_64 (x : Memory) : x.honest 64 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_65 (x : Memory) : x.honest 65 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_66 (x : Memory) : x.honest 66 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_67 (x : Memory) : x.honest 67 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_68 (x : Memory) : x.honest 68 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_69 (x : Memory) : x.honest 69 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_70 (x : Memory) : x.honest 70 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_71 (x : Memory) : x.honest 71 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_72 (x : Memory) : x.honest 72 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_73 (x : Memory) : x.honest 73 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_74 (x : Memory) : x.honest 74 = ((x.addrLo / 4 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_75 (x : Memory) : x.honest 75 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_76 (x : Memory) : x.honest 76 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_77 (x : Memory) : x.honest 77 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_78 (x : Memory) : x.honest 78 = (((x.baseLo : Nat) + 65536 * (x.baseHi : Nat)) * ((x.valLo : Nat) + 65536 * (x.valHi : Nat)) * 943718400 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_79 (x : Memory) : x.honest 79 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_80 (x : Memory) : x.honest 80 = ((x.addrHi - 64 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_81 (x : Memory) : x.honest 81 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_82 (x : Memory) : x.honest 82 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_83 (x : Memory) : x.honest 83 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_84 (x : Memory) : x.honest 84 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_85 (x : Memory) : x.honest 85 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_86 (x : Memory) : x.honest 86 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_87 (x : Memory) : x.honest 87 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_88 (x : Memory) : x.honest 88 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_89 (x : Memory) : x.honest 89 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_90 (x : Memory) : x.honest 90 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_91 (x : Memory) : x.honest 91 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_92 (x : Memory) : x.honest 92 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_93 (x : Memory) : x.honest 93 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_94 (x : Memory) : x.honest 94 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_95 (x : Memory) : x.honest 95 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_96 (x : Memory) : x.honest 96 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_97 (x : Memory) : x.honest 97 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_98 (x : Memory) : x.honest 98 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_99 (x : Memory) : x.honest 99 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_100 (x : Memory) : x.honest 100 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_101 (x : Memory) : x.honest 101 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_102 (x : Memory) : x.honest 102 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_103 (x : Memory) : x.honest 103 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_104 (x : Memory) : x.honest 104 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_105 (x : Memory) : x.honest 105 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_106 (x : Memory) : x.honest 106 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_107 (x : Memory) : x.honest 107 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_108 (x : Memory) : x.honest 108 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_109 (x : Memory) : x.honest 109 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_110 (x : Memory) : x.honest 110 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_111 (x : Memory) : x.honest 111 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_112 (x : Memory) : x.honest 112 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_113 (x : Memory) : x.honest 113 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_114 (x : Memory) : x.honest 114 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_115 (x : Memory) : x.honest 115 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_116 (x : Memory) : x.honest 116 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_117 (x : Memory) : x.honest 117 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_118 (x : Memory) : x.honest 118 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_119 (x : Memory) : x.honest 119 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_120 (x : Memory) : x.honest 120 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_121 (x : Memory) : x.honest 121 = (0 : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_122 (x : Memory) : x.honest 122 = ((x.frame.pcCarry : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_123 (x : Memory) : x.honest 123 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_124 (x : Memory) : x.honest 124 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := by rfl
@[unified_honest] theorem col_125 (x : Memory) : x.honest 125 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := by rfl
-- END generated columns

theorem columns (x : Memory) : x.frame.Columns x.honest :=
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

/-- The address low-limb sum, as the circuit states it. -/
theorem low (x : Memory) :
    (x.baseLo : ZMod babyBearModulus) + (x.immLo : Nat) - (x.addrLo : Nat) - 65536 * (x.carryLo : Nat) = 0 := by
  have e := cast_mod x.sumLo 65536
  simp only [addrLo, carryLo, sumLo] at e ⊢
  push_cast at e ⊢; linear_combination -e

/-- The address high-limb sum, as the circuit states it. -/
theorem high (x : Memory) :
    (x.baseHi : ZMod babyBearModulus) + (x.immHi : Nat) + (x.carryLo : Nat) - (x.addrHi : Nat) -
      65536 * (x.carryHi : Nat) = 0 := by
  have e := cast_mod x.sumHi 65536
  simp only [addrHi, carryHi, sumHi] at e ⊢
  push_cast at e ⊢; linear_combination -e

theorem align {x : Memory} (hx : x.Valid) :
    4 * ((x.addrLo / 4 : Nat) : ZMod babyBearModulus) - (x.addrLo : Nat) = 0 := by
  have e : 4 * (x.addrLo / 4) = x.addrLo := by have := hx.aligned; omega
  have e' := congrArg (Nat.cast : Nat → ZMod babyBearModulus) e
  push_cast at e'; linear_combination e'

theorem window {x : Memory} (hx : x.Valid) :
    ((x.addrHi - 64 : Nat) : ZMod babyBearModulus) - ((x.addrHi : Nat) - 64) = 0 := by
  rw [Nat.cast_sub hx.ram]; push_cast; ring

theorem complete_core (x : Memory) (hx : x.Valid) (t : Table (ZMod babyBearModulus) (fields 10))
    (zero : ZeroRow t) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (importedConstraints t) := by
  have hf := hx.clock
  have := hx.reg; have := hx.valLo; have := hx.valHi; have := hf.pcHi
  have : x.frame.pcHi < 65536 := by have := hf.pcHi; unfold Frame.finalPcHi at this; omega
  have : x.frame.finalPcLo < 65536 := Nat.mod_lt _ (by decide)
  have : x.addrLo < 65536 := Nat.mod_lt _ (by decide)
  have : x.addrHi < 65536 := Nat.mod_lt _ (by decide)
  have hcl : x.carryLo ≤ 1 := by have := hx.baseLo; have := hx.immLo; unfold carryLo sumLo; omega
  have hch : x.carryHi ≤ 1 := by
    have := hx.baseHi; have := hx.immHi; unfold carryHi sumHi; omega
  have hl := low x; have hh := high x; have ha := align hx; have hw := window hx
  simp only [importedConstraints, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  -- goals 1-120: equations; 121-133: 16-bit ranges; 134-138: setup lookups
  iterate 5
    on_goal 134 =>
      refine zero _ _ ?_
      apply Vector.ext
      intro j hj
      interval_cases j <;> simp [Expression.eval, environment, unified_honest]
  all_goals cases hst : x.store
  all_goals first
    | exact True.intro
    | (apply range16_contains
       simp only [Expression.eval, environment, unified_honest, hst, Bool.false_eq_true, ↓reduceIte,
         cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_add, one_mul, Arithmetic.limbBase]
       first
         | (rw [ZMod.val_natCast]; exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega))
         | (simp only [ZMod.val_zero]; decide))
    | skip
  all_goals simp only [Expression.eval, environment, unified_honest, hst, Bool.false_eq_true, ↓reduceIte,
    cast_ofNat, cast_negSucc, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero,
    zero_mul, add_zero, zero_add, mul_one, one_mul]
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
    | linear_combination hl
    | linear_combination hh
    | linear_combination ha
    | linear_combination hw

theorem complete (x : Memory) (hx : x.Valid) (hf : x.frame.Valid)
    (t : Table (ZMod babyBearModulus) (fields 10)) (zero : ZeroRow t) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (clockConstraints t) :=
  holds_append (complete_core x hx t zero) (Frame.timestamps hf x.columns)

end Memory

end Airbender.UnifiedReduced.Completeness
