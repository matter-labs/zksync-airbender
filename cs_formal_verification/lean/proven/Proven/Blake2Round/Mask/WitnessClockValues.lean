module
public import Proven.Blake2Round.Mask.WitnessData

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option maxRecDepth 32768

theorem zero_timestamp_values : ∀ i : Fin 89,
    let query := (FlatOperation.lookups (importedConstraintsTimestampLookups (p := babyBearModulus))).get
      ⟨i.val, by rw [timestamp_count]; exact i.isLt⟩
    query.entry.map (Verification.environment zeroAssignment) =
      query.entry.map (Verification.environment (zeroSource.assignment (p := babyBearModulus))) := by
  decide +kernel


end Airbender.Blake2Round.Mask.Proofs
