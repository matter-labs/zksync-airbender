import Airbender.Proofs.UnifiedReduced.ControlQueries
import Airbender.Proofs.UnifiedReduced.ControlKey

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem control_conditional_lookup [Fact p.Prime] (hp : 4194304 ≤ p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 21 + w 22 + w 23 + w 24 = 1)
    (binary : w 26 = 0 ∧ w 27 = 0) (rom : w 87 = 0)
    (leftHi : (w 37).val < 65536) (rightHi : (w 60).val < 65536)
    (funct : (w 10).val < 8) :
    (pairLookup conditionalTable
      (.var ⟨60⟩ + .const 65536 * .var ⟨58⟩ + .const 131072 * .var ⟨53⟩ +
        .const 262144 * .var ⟨57⟩ + .const 524288 * .var ⟨10⟩) (.var ⟨59⟩)).Contains
      (Verification.environment w) := by
  have values := control_lookup_values hp holds selected binary rom
  have leftSign : (w 58).val = (w 37).val / 32768 := by
    rw [values.2.1, ZMod.val_natCast_of_lt (by omega)]
  have rightSign : (w 61).val = (w 60).val / 32768 := by
    rw [values.2.2.1, ZMod.val_natCast_of_lt (by omega)]
  have borrow := boolean_val (local_flags holds 21)
  change (w 53).val ≤ 1 at borrow
  have equal : (w 57).val < 2 := by
    rw [values.1]
    split <;> simp [ZMod.val_one'' (by omega : p ≠ 1)]
  have leftBound : (w 58).val < 2 := by omega
  have rightBound : (w 61).val < 2 := by omega
  let original := (w 60).val + 65536 * (w 58).val + 131072 * (w 53).val +
    262144 * (w 57).val + 524288 * (w 10).val
  let native := (w 61).val + 2 * (w 58).val + 4 * (w 53).val +
    8 * (w 57).val + 16 * (w 10).val
  have originalBound : original < 4194304 := by dsimp [original]; omega
  have nativeBound : native < 128 := by dsimp [native]; omega
  have originalCast : (original : ZMod p) =
      w 60 + 65536 * w 58 + 131072 * w 53 + 262144 * w 57 + 524288 * w 10 := by
    simp only [original, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
  have nativeCast : (native : ZMod p) =
      w 61 + 2 * w 58 + 4 * w 53 + 8 * w 57 + 16 * w 10 := by
    simp only [native, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
  have nativeValue : (w 61 + 2 * w 58 + 4 * w 53 + 8 * w 57 + 16 * w 10).val = native := by
    rw [← nativeCast, ZMod.val_natCast_of_lt (by omega)]
  have same : conditionalValue original = conditionalValue (Setup.conditionalKey native) := by
    dsimp only [original, native]
    rw [rightSign]
    exact conditional_sign_key rightHi leftBound (by omega) equal funct
  apply (pairLookup conditionalTable _ (.var ⟨59⟩)).table.implied_by_completeness
  apply (Lookup.completeness_def conditionalTable (Verification.environment w)
    (.var ⟨60⟩ + .const 65536 * .var ⟨58⟩ + .const 131072 * .var ⟨53⟩ +
      .const 262144 * .var ⟨57⟩ + .const 524288 * .var ⟨10⟩, .var ⟨59⟩)).mpr
  simp only [conditionalTable_characterization]
  with_unfolding_all change ∃ i : Fin 4194304,
    (w 60 + 65536 * w 58 + 131072 * w 53 + 262144 * w 57 + 524288 * w 10, w 59) =
    ((i.val : ZMod p), (conditionalValue i.val : ZMod p))
  refine ⟨⟨original, originalBound⟩, ?_⟩
  apply Prod.ext
  · exact originalCast.symm
  · simpa only [nativeValue, ← same] using values.2.2.2.2.1

end Airbender.UnifiedReduced.Proofs
