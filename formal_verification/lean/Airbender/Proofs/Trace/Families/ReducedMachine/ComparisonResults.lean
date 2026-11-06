import Airbender.Proofs.Trace.Families.ReducedMachine.ComparisonValues
import Airbender.Proofs.ReducedMachine.NativeComparisonDecodedResult

namespace Airbender.ReducedMachine.NativeComparisonRangeProofs
open Native Trace Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Public initialization/decoding and native matching discharge every internal
    comparison range premise. Actual read words are not yet pre-row Sail GPRs. -/
theorem image_comparison_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ComparisonMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : comparisonDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ComparisonDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before comparisonDecoderFields ∧
      row.decoderQuery = entry.query ∧ ComparisonDecoded row.assignment entry ∧
      candidateWord row.assignment = Word.ofBitVec (entry.data.family.result
        (sourceWord row.assignment).toBitVec (operandWord row.assignment).toBitVec) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (sourceWord row.assignment).toBitVec (operandWord row.assignment).toBitVec) := by
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  obtain ⟨entry,found,source,query,fields⟩ := NativeComparisonDecoderProofs.trace_decoding image accepted decoded row present
  refine ⟨entry,found,source,query,fields,?_⟩
  cases row with
  | mk family w =>
    cases family
    have first := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    have second := ranges importedConstraintsMemoryPorts[1] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at first second
    change (sourceWord w).Bounded at first
    change (⟨(w 37).val,(w 38).val⟩ : Word).Bounded at second
    exact NativeComparisonResultProofs.decoded_result (accepted.constraints _ present) source.fields query first second

end Airbender.ReducedMachine.NativeComparisonRangeProofs
