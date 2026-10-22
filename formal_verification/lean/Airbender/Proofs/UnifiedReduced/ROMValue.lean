import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.WordROM

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem word_rom_value [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {initial : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (active : w 4 = 1) (load : w 28 = 1) (rom : w 54 = 1) :
    (w 39).val < 64 ∧ ((w 38).val + 65536 * (w 39).val) % 4 = 0 ∧
      (Word.mk (w 50).val (w 51).val).toBitVec =
        ROM.words initial (((w 38).val + 65536 * (w 39).val) / 4) := by
  have excluded := dispatch_exclusive (by omega) holds active 16 load
  have store : w 29 = 0 := excluded 17 (by decide)
  have other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 :=
    ⟨excluded 10 (by decide), excluded 11 (by decide), excluded 12 (by decide), excluded 13 (by decide)⟩
  have binary : w 26 = 0 ∧ w 27 = 0 := ⟨excluded 14 (by decide), excluded 15 (by decide)⟩
  have gate := Verification.assertion_of_holds holds ⟨42, by rw [constraint_count]; decide⟩
  have enabled : w 87 = 1 := by
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, load, rom] at gate
    linear_combination gate
  have equations (i : Fin 4) := Verification.assertion_of_holds holds
    ⟨48 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have t := equations 0; have a := equations 1; have b := equations 2; have c := equations 3
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    active, enabled, other.1, other.2.1, other.2.2.1, other.2.2.2, binary.1, binary.2] at t a b c
  have tag : w 88 = 34 := by linear_combination t
  have key : w 89 = w 57 + 65536 * w 58 := by linear_combination a
  have resultLow : w 90 = w 50 := by linear_combination b
  have resultHigh : w 91 = w 51 := by linear_combination c
  have low := Verification.assertion_of_holds holds ⟨35, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨37, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, load] at low high
  have addressLow : w 57 = w 38 := by linear_combination low
  have addressHigh : w 58 = w 39 := by linear_combination high
  have classify := (word_rom_selection (by omega) false holds load store).1
  change w 54 = (if (w 39).val < 64 then 1 else 0) at classify
  have inside : (w 39).val < 64 := by
    by_contra outside
    rw [if_neg outside, rom] at classify
    exact one_ne_zero classify
  have lowBound := Verification.range16_bound (Verification.lookup_of_holds holds ⟨6, by rw [lookup_count]; decide⟩)
  have lowBound : (w 38).val < 65536 := by
    simpa [Expression.eval, Verification.environment, limbBase] using lowBound
  have packed : (w 89).val = (w 38).val + 65536 * (w 39).val := by
    have cast : w 89 = (((w 38).val + 65536 * (w 39).val : Nat) : ZMod p) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val,
        addressLow, addressHigh] using key
    rw [cast, ZMod.val_natCast_of_lt (by omega)]
  have query := Verification.lookup_of_holds holds ⟨13, by rw [lookup_count]; decide⟩
  have result := Setup.Proofs.rom_lookup hp query
    (by simpa [Expression.eval, Verification.environment] using tag)
  have result : (w 89).val % 4 = 0 ∧ (Word.mk (w 50).val (w 51).val).toBitVec =
      ROM.words initial ((w 89).val / 4) := by
    simpa [Expression.eval, Verification.environment, resultLow, resultHigh] using And.intro result.2.1 result.2.2.1
  exact ⟨inside, packed ▸ result⟩

end Airbender.UnifiedReduced.Proofs
