import Airbender.Review.Helpers.Tables.NativeScalars
import Airbender.Proofs.AddSub.ArtifactChecks
import Airbender.Proofs.WordMemory.ArtifactChecks

namespace Tests.NativeScalars
open Airbender Verification NativeSetup

/-- Exact shared scalar geometry, including compiled column positions. -/
theorem geometry : scalarsRange16.length = 65536 ∧ scalarsTimestamp19.length = 524288 ∧
    scalarsRange16.nativeOffset = 0 ∧ scalarsTimestamp19.nativeOffset = 1 := by decide

/-- Both pinned compiled families place these scalar columns at the same offsets. -/
theorem compiled_placements :
    AddSub.importedConstraintsSetupColumns.range16 = scalarsRange16.nativeOffset ∧
    AddSub.importedConstraintsSetupColumns.timestamp19 = scalarsTimestamp19.nativeOffset ∧
    WordMemory.importedConstraintsSetupColumns.range16 = scalarsRange16.nativeOffset ∧
    WordMemory.importedConstraintsSetupColumns.timestamp19 = scalarsTimestamp19.nativeOffset := by decide

theorem prefix_boundaries :
    scalarsRange16.rowNat ⟨65535, by decide⟩ = #v[65535] ∧
    scalarsTimestamp19.rowNat ⟨524287, by decide⟩ = #v[524287] := by decide +kernel

/-- All zero filler remains in the active domain, including its last row. -/
theorem active_padding :
    scalarRow (p := mersenne31Modulus) .range16 ⟨65536, by decide⟩ = 0 ∧
    scalarRow (p := mersenne31Modulus) .timestamp19 ⟨524288, by decide⟩ = 0 ∧
    scalarRow (p := mersenne31Modulus) .range16 ⟨16777214, by decide⟩ = 0 ∧
    scalarRow (p := mersenne31Modulus) .timestamp19 ⟨16777214, by decide⟩ = 0 := by decide +kernel

theorem native_bounds :
    ScalarContains .range16 (65535 : ZMod mersenne31Modulus) ∧
    ¬ ScalarContains .range16 (65536 : ZMod mersenne31Modulus) ∧
    ScalarContains .timestamp19 (524287 : ZMod mersenne31Modulus) ∧
    ¬ ScalarContains .timestamp19 (524288 : ZMod mersenne31Modulus) := by
  simp only [native_scalar_lookup]
  decide

/-- Exported regional columns have no row beyond their actual finite prefixes. -/
theorem finite_endpoints : scalarsRange16.columns[0].get? 65536 = none ∧
    scalarsTimestamp19.columns[0].get? 524288 = none := by decide +kernel

end Tests.NativeScalars
