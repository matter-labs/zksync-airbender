import Airbender.Proofs.Keccak.SplitParityIotaPacking

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Both actual native control-register high limbs are zero. -/
theorem parity_control_high_limbs (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) :
    w 4 = 0 ∧ w 6 = 0 := by
  cases cached
  all_goals
    have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    have readHigh := Verification.assertion_of_holds core ⟨1, by change 1 < 20; decide⟩
    have writeHigh := Verification.assertion_of_holds core ⟨2, by change 2 < 20; decide⟩
    change w 4 = 0 at readHigh
    change w 6 = 0 at writeHigh
    exact ⟨readHigh, writeHigh⟩

/-- The actual low bytes outside the iota mask equal their written byte values. -/
theorem parity_iota_unchanged_low (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (index : Fin 2) :
    parityIotaInputLow w ⟨index.val + 1, by omega⟩ =
      parityIotaOutputByte cached w (parityIotaLimb ⟨index.val + 1, by omega⟩) false := by
  cases cached
  all_goals
    have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    have equation := Verification.assertion_of_holds core ⟨3 + index.val, by change 3 + index.val < 20; omega⟩
    fin_cases index
  all_goals
    norm_num [parityIotaOutputByte, parityIotaLimb]
    dsimp only [ColumnParity.importedConstraints, ColumnParityCached.importedConstraints,
      FlatOperation.constraints, List.get, Expression.eval, Verification.environment] at equation
    dsimp only [parityIotaInputLow, parityIotaOutputByte, parityIotaLimb, parityNibble,
      columnParityQueryEntry, columnParityQuery, ColumnParity.importedConstraints,
      ColumnParityCached.importedConstraints, FlatOperation.lookups, List.get,
      Expression.eval, Verification.environment]
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] at equation ⊢
    linear_combination equation

/-- The native first lane retains limb two without a byte lookup. -/
theorem parity_iota_unchanged_limb (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) :
    parityLaneLimb cached false w 0 2 = parityLaneLimb cached true w 0 2 := by
  cases cached
  all_goals
    have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    have equation := Verification.assertion_of_holds core ⟨5, by change 5 < 20; decide⟩
    dsimp only [ColumnParity.importedConstraints, ColumnParityCached.importedConstraints,
      FlatOperation.constraints, List.get, Expression.eval, Verification.environment] at equation
    dsimp only [parityLaneLimb, Row.ports, WordColumns.evaluate,
      ColumnParity.importedConstraintsMemoryPorts, ColumnParityCached.importedConstraintsMemoryPorts]
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] at equation ⊢
    linear_combination equation

end Airbender.Keccak.Split.Native.Proofs
