module
public import Proven.Blake2Round.Mask.WitnessData

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option maxRecDepth 32768

theorem zero_lookup_values : ∀ i : Fin 194,
    let query := (FlatOperation.lookups (importedConstraints (p := babyBearModulus) setupTable)).get
      ⟨i.val, by rw [lookup_count]; exact i.isLt⟩
    query.entry.map (Verification.environment zeroAssignment) =
      query.entry.map (Verification.environment (zeroSource.assignment (p := babyBearModulus))) := by
  decide +kernel

theorem zero_holds : FlatOperation.ConstraintsHoldFlat (Verification.environment zeroAssignment)
    (importedConstraints setupTable) := by
  apply NonVacuous.holds_of_get
  · intro i bound
    exact zero_asserts ⟨i, by rwa [constraint_count] at bound⟩
  · intro i bound
    have old := NonVacuous.Blake2RoundSpan.lookups (p := babyBearModulus) rfl zeroSource_valid i bound
    have same := zero_lookup_values ⟨i, by rwa [lookup_count] at bound⟩
    dsimp only at same
    unfold Lookup.Contains at old ⊢
    rw [same]
    exact old


end Airbender.Blake2Round.Mask.Proofs
