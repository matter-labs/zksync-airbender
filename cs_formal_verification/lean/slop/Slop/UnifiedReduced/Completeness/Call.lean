import Slop.UnifiedReduced.Completeness.Arith

/-! Completeness of the unified circuit for its delegation-call row (the CSR access that
    issues a precompile request): the honest assignment satisfies every equation, range
    query and (disabled) setup lookup, for any setup table holding the all-zero query.
    Proved once, symbolically. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true
set_option maxRecDepth 16384

/-- Inputs of one honest delegation-call row: the CSR index travels through the second
    port's address column (`csr`, a field element below 2^16), `a*` is the first source
    register's value and `old*` the destination's previous value. The call reads and
    writes no word: the CSR port's value columns and previous clock are zero. -/
structure Call where
  frame : Frame
  rs1 : Nat
  rd : Nat
  csr : ZMod babyBearModulus
  aLo : Nat
  aHi : Nat
  oldLo : Nat
  oldHi : Nat

namespace Call

structure Valid (x : Call) : Prop where
  clock : x.frame.Clock
  rd : x.rd < 65536
  csr : x.csr.val < 65536
  prev1Lo : x.frame.prev1Lo = 0
  prev1Hi : x.frame.prev1Hi = 0

/-- The honest witness columns of a delegation-call row. -/
def honest (x : Call) : Nat → ZMod babyBearModulus
  | 0 => (x.frame.pcLo : Nat) | 1 => (x.frame.pcHi : Nat)
  | 2 => (x.frame.tsLo : Nat) | 3 => (x.frame.tsHi : Nat)
  | 4 | 18 => 1
  | 5 => (x.rs1 : Nat)
  | 6 | 38 => x.csr
  | 7 | 44 => (x.rd : Nat)
  | 30 => (x.frame.finalPcLo : Nat) | 31 => (x.frame.finalPcHi : Nat)
  | 32 => (x.frame.finalTsLo : Nat) | 33 => (x.frame.finalTsHi : Nat)
  | 34 => (x.frame.prev0Lo : Nat) | 35 => (x.frame.prev0Hi : Nat)
  | 40 => (x.frame.prev1Lo : Nat) | 41 => (x.frame.prev1Hi : Nat)
  | 46 => (x.frame.prev2Lo : Nat) | 47 => (x.frame.prev2Hi : Nat)
  | 36 => (x.aLo : Nat) | 37 => (x.aHi : Nat)
  | 48 => (x.oldLo : Nat) | 49 => (x.oldHi : Nat)
  | 122 => (x.frame.pcCarry : Nat)
  | 123 => (x.frame.borrow0 : Nat) | 124 => (x.frame.borrow1 : Nat)
  | 125 => (x.frame.borrow2 : Nat)
  | _ => 0

-- BEGIN generated columns
-- generated: one rfl lemma per column (keeps `simp` off the column match)
@[unified_honest] theorem col_0 (x : Call) : x.honest 0 = ((x.frame.pcLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_1 (x : Call) : x.honest 1 = ((x.frame.pcHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_2 (x : Call) : x.honest 2 = ((x.frame.tsLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_3 (x : Call) : x.honest 3 = ((x.frame.tsHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_4 (x : Call) : x.honest 4 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_5 (x : Call) : x.honest 5 = ((x.rs1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_6 (x : Call) : x.honest 6 = (x.csr : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_7 (x : Call) : x.honest 7 = ((x.rd : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_8 (x : Call) : x.honest 8 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_9 (x : Call) : x.honest 9 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_10 (x : Call) : x.honest 10 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_11 (x : Call) : x.honest 11 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_12 (x : Call) : x.honest 12 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_13 (x : Call) : x.honest 13 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_14 (x : Call) : x.honest 14 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_15 (x : Call) : x.honest 15 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_16 (x : Call) : x.honest 16 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_17 (x : Call) : x.honest 17 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_18 (x : Call) : x.honest 18 = (1 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_19 (x : Call) : x.honest 19 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_20 (x : Call) : x.honest 20 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_21 (x : Call) : x.honest 21 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_22 (x : Call) : x.honest 22 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_23 (x : Call) : x.honest 23 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_24 (x : Call) : x.honest 24 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_25 (x : Call) : x.honest 25 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_26 (x : Call) : x.honest 26 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_27 (x : Call) : x.honest 27 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_28 (x : Call) : x.honest 28 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_29 (x : Call) : x.honest 29 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_30 (x : Call) : x.honest 30 = ((x.frame.finalPcLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_31 (x : Call) : x.honest 31 = ((x.frame.finalPcHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_32 (x : Call) : x.honest 32 = ((x.frame.finalTsLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_33 (x : Call) : x.honest 33 = ((x.frame.finalTsHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_34 (x : Call) : x.honest 34 = ((x.frame.prev0Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_35 (x : Call) : x.honest 35 = ((x.frame.prev0Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_36 (x : Call) : x.honest 36 = ((x.aLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_37 (x : Call) : x.honest 37 = ((x.aHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_38 (x : Call) : x.honest 38 = (x.csr : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_39 (x : Call) : x.honest 39 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_40 (x : Call) : x.honest 40 = ((x.frame.prev1Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_41 (x : Call) : x.honest 41 = ((x.frame.prev1Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_42 (x : Call) : x.honest 42 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_43 (x : Call) : x.honest 43 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_44 (x : Call) : x.honest 44 = ((x.rd : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_45 (x : Call) : x.honest 45 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_46 (x : Call) : x.honest 46 = ((x.frame.prev2Lo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_47 (x : Call) : x.honest 47 = ((x.frame.prev2Hi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_48 (x : Call) : x.honest 48 = ((x.oldLo : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_49 (x : Call) : x.honest 49 = ((x.oldHi : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_50 (x : Call) : x.honest 50 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_51 (x : Call) : x.honest 51 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_52 (x : Call) : x.honest 52 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_53 (x : Call) : x.honest 53 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_54 (x : Call) : x.honest 54 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_55 (x : Call) : x.honest 55 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_56 (x : Call) : x.honest 56 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_57 (x : Call) : x.honest 57 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_58 (x : Call) : x.honest 58 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_59 (x : Call) : x.honest 59 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_60 (x : Call) : x.honest 60 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_61 (x : Call) : x.honest 61 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_62 (x : Call) : x.honest 62 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_63 (x : Call) : x.honest 63 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_64 (x : Call) : x.honest 64 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_65 (x : Call) : x.honest 65 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_66 (x : Call) : x.honest 66 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_67 (x : Call) : x.honest 67 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_68 (x : Call) : x.honest 68 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_69 (x : Call) : x.honest 69 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_70 (x : Call) : x.honest 70 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_71 (x : Call) : x.honest 71 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_72 (x : Call) : x.honest 72 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_73 (x : Call) : x.honest 73 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_74 (x : Call) : x.honest 74 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_75 (x : Call) : x.honest 75 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_76 (x : Call) : x.honest 76 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_77 (x : Call) : x.honest 77 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_78 (x : Call) : x.honest 78 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_79 (x : Call) : x.honest 79 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_80 (x : Call) : x.honest 80 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_81 (x : Call) : x.honest 81 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_82 (x : Call) : x.honest 82 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_83 (x : Call) : x.honest 83 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_84 (x : Call) : x.honest 84 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_85 (x : Call) : x.honest 85 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_86 (x : Call) : x.honest 86 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_87 (x : Call) : x.honest 87 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_88 (x : Call) : x.honest 88 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_89 (x : Call) : x.honest 89 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_90 (x : Call) : x.honest 90 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_91 (x : Call) : x.honest 91 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_92 (x : Call) : x.honest 92 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_93 (x : Call) : x.honest 93 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_94 (x : Call) : x.honest 94 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_95 (x : Call) : x.honest 95 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_96 (x : Call) : x.honest 96 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_97 (x : Call) : x.honest 97 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_98 (x : Call) : x.honest 98 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_99 (x : Call) : x.honest 99 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_100 (x : Call) : x.honest 100 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_101 (x : Call) : x.honest 101 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_102 (x : Call) : x.honest 102 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_103 (x : Call) : x.honest 103 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_104 (x : Call) : x.honest 104 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_105 (x : Call) : x.honest 105 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_106 (x : Call) : x.honest 106 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_107 (x : Call) : x.honest 107 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_108 (x : Call) : x.honest 108 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_109 (x : Call) : x.honest 109 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_110 (x : Call) : x.honest 110 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_111 (x : Call) : x.honest 111 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_112 (x : Call) : x.honest 112 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_113 (x : Call) : x.honest 113 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_114 (x : Call) : x.honest 114 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_115 (x : Call) : x.honest 115 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_116 (x : Call) : x.honest 116 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_117 (x : Call) : x.honest 117 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_118 (x : Call) : x.honest 118 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_119 (x : Call) : x.honest 119 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_120 (x : Call) : x.honest 120 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_121 (x : Call) : x.honest 121 = (0 : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_122 (x : Call) : x.honest 122 = ((x.frame.pcCarry : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_123 (x : Call) : x.honest 123 = ((x.frame.borrow0 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_124 (x : Call) : x.honest 124 = ((x.frame.borrow1 : Nat) : ZMod babyBearModulus) := rfl
@[unified_honest] theorem col_125 (x : Call) : x.honest 125 = ((x.frame.borrow2 : Nat) : ZMod babyBearModulus) := rfl
-- END generated columns

theorem columns (x : Call) : x.frame.Columns x.honest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem complete_core (x : Call) (hx : x.Valid) (t : Table (ZMod babyBearModulus) (fields 10))
    (zero : ZeroRow t) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (importedConstraints t) := by
  have hf := hx.clock
  have := hx.rd; have hcsr := hx.csr; have := hf.pcHi
  have : x.frame.pcHi < 65536 := by have := hf.pcHi; unfold Frame.finalPcHi at this; omega
  have : x.frame.finalPcLo < 65536 := Nat.mod_lt _ (by decide)
  have h40 := hx.prev1Lo; have h41 := hx.prev1Hi
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
         | exact hcsr
         | (rw [ZMod.val_natCast]; exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega))
         | (simp only [ZMod.val_zero]; decide))
    | skip
  all_goals simp only [Expression.eval, environment, unified_honest, h40, h41, cast_ofNat, cast_negSucc,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul]
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

theorem complete (x : Call) (hx : x.Valid) (hf : x.frame.Valid)
    (t : Table (ZMod babyBearModulus) (fields 10)) (zero : ZeroRow t) :
    FlatOperation.ConstraintsHoldFlat (environment x.honest) (clockConstraints t) :=
  holds_append (complete_core x hx t zero) (Frame.timestamps hf x.columns)

end Call

end Airbender.UnifiedReduced.Completeness
