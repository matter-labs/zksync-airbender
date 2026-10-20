import Tests.ShiftValuesFixture
import Airbender.Review.Trace.Families.ShiftBinop.Sources
import Tests.ShiftContributions

namespace Tests.ShiftValues
open Airbender Arithmetic Trace ShiftBinop Tests.ShiftHistoryFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original public bytes, native decoding and initialized matching derive all
    twenty-four complete rows' read/write and actual terminal word bounds. -/
theorem public_bounds (sample : Fin 24) :
    (∀ row ∈ (trace sample).rows, ∀ port ∈ row.ports,
      (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ (trace sample).rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ (trace sample).terminalMemory, token.word.Bounded) :=
  ShiftBinop.public_value_bounds (ShiftValuesFixture.program_image sample)
    (ShiftValuesFixture.public_inputs sample) (accepted sample) (ShiftValuesFixture.decoded sample)

theorem source_bounds (sample : Fin 24) : (left (ShiftHistoryRows.assignment sample)).Bounded := by
  have bounded := (public_bounds sample).1 (nativeRow sample) (by simp [trace])
    importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at bounded
  exact bounded

/-- All complete initialized rows apply the public original-code source claim. -/
theorem public_sources (sample : Fin 24) :
    ∃ entry ∈ NativeSetup.setup.program,
      entry.SourceWith (ShiftValuesFixture.before sample) ShiftBinop.decoderFields ∧
      (nativeRow sample).decoderQuery = entry.query ∧
      ∀ kind, entry.data.family = kind.operation →
        ShiftSourceBinding (ShiftHistoryRows.assignment sample) kind :=
  ShiftBinop.public_shift_sources (ShiftValuesFixture.program_image sample)
    (ShiftValuesFixture.public_inputs sample) (accepted sample) (ShiftValuesFixture.decoded sample)
    _ (by simp [trace])

/-- Twelve native shift cases use initialized source bounds, retaining canonical
    key quotient/remainder, zero inactive slots and bounded discarded results. -/
theorem concrete_sources (i : Fin 12) :
    ShiftSourceBinding (ShiftHistoryRows.assignment (ShiftContributions.sample i))
      (ShiftContributions.kind i) := by
  apply ShiftBinop.Proofs.shift_source_binding _ (source_bounds _)
  apply ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[(ShiftContributions.sample i).val])
    (ShiftHistoryRows.native_constraints _) _ _ _ _
  · fin_cases i <;> rfl
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> rfl

end Tests.ShiftValues
