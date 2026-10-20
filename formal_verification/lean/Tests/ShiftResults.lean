import Tests.ShiftValues
import Airbender.Review.Trace.Families.ShiftBinop.Theorems

namespace Tests.ShiftResults
open Airbender Arithmetic Trace ShiftBinop Tests.ShiftHistoryFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All twenty-four accepted initialized ordinary/x0 traces exercise the short
    public numerical result theorem with actual original Sail code and seeds. -/
theorem public_results (sample : Fin 24) :
    ∀ row ∈ (trace sample).rows, ∃ entry ∈ NativeSetup.setup.program,
      entry.SourceWith (ShiftValuesFixture.before sample) ShiftBinop.decoderFields ∧
      row.decoderQuery = entry.query ∧
      selectedWord row.assignment = Word.ofBitVec
        (entry.data.family.result (left row.assignment) (right row.assignment)) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (left row.assignment) (right row.assignment)) :=
  ShiftBinop.public_native_results (ShiftValuesFixture.program_image sample)
    (ShiftValuesFixture.public_inputs sample) (accepted sample) (ShiftValuesFixture.decoded sample)

/-- Identify each actual decoded entry, with its source bound supplied by the
    initialized public range theorem rather than a local fixture assumption. -/
theorem concrete_results (sample : Fin 24) :
    selectedWord (ShiftHistoryRows.assignment sample) = Word.ofBitVec
      (NativeSetup.entries[sample.val].data.family.result
        (left (ShiftHistoryRows.assignment sample)) (right (ShiftHistoryRows.assignment sample))) ∧
    writtenWord (ShiftHistoryRows.assignment sample) =
      if NativeSetup.entries[sample.val].data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (NativeSetup.entries[sample.val].data.family.result
          (left (ShiftHistoryRows.assignment sample)) (right (ShiftHistoryRows.assignment sample))) := by
  apply ShiftBinop.Proofs.entry_numerical_result
    (ShiftHistoryRows.native_constraints sample) _ _ (ShiftValues.source_bounds sample)
  · fin_cases sample <;> rfl
  · fin_cases sample <;> decide +kernel

def expected : Vector Nat 12 := #v[524280,268443647,4026540031,
  2147549180,2147549183,3,2147483648,1,4294967295,
  2147418112,4294967295,2047]

/-- Concrete whole selected results retain SRA sign extension, SRAI 1055→31,
    immediate sign extension and all twelve actual discarded x0 destinations. -/
theorem concrete_outputs (sample : Fin 24) :
    (selectedWord (ShiftHistoryRows.assignment sample)).value = expected[sample.val % 12] ∧
      (writtenWord (ShiftHistoryRows.assignment sample)).value =
        if sample.val < 12 then expected[sample.val % 12] else 0 := by
  rw [(concrete_results sample).1,(concrete_results sample).2]
  fin_cases sample <;> decide +kernel

end Tests.ShiftResults
