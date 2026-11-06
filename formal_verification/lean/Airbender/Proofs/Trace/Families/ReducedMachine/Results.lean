import Airbender.Proofs.Trace.Families.ReducedMachine.Values
import Airbender.Proofs.ReducedMachine.NativeShiftResult

namespace Airbender.ReducedMachine.NativeShiftRangeProofs
open Native Trace Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Initialized public history discharges the local numerical result's source
    premise. Actual read words are not yet original pre-row Sail GPRs. -/
theorem image_shift_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧
      row.decoderQuery = entry.query ∧ ShiftDecoded row.assignment entry ∧
      candidateWord row.assignment = Word.ofBitVec
        (entry.data.family.result (sourceWord row.assignment).toBitVec
          ((operandWord row.assignment).toBitVec.extractLsb' 0 5).toNat) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (sourceWord row.assignment).toBitVec
          ((operandWord row.assignment).toBitVec.extractLsb' 0 5).toNat) := by
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  have bounds := ranges importedConstraintsMemoryPorts[0] (by
    cases row with
    | mk family w => cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at bounds
  change (sourceWord row.assignment).Bounded at bounds
  obtain ⟨entry,found,source,query,fields⟩ := NativeShiftDecoderProofs.trace_decoding image accepted decoded row present
  have native := accepted.constraints row present
  refine ⟨entry,found,source,query,fields,?_⟩
  cases row with
  | mk family w =>
    cases family
    exact NativeShiftResultProofs.decoded_result native source.fields query bounds

end Airbender.ReducedMachine.NativeShiftRangeProofs
