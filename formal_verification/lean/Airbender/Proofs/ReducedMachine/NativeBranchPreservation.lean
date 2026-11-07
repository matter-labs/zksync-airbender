import Airbender.Proofs.ReducedMachine.NativeBranchDecoder
import Airbender.Proofs.ReducedMachine.NativeBranchFields
import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Proofs.Trace.Values

namespace Airbender.ReducedMachine.NativeBranchPreservationProofs
open Native Trace Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual present dummy-port write is zero regardless of source/read ranges. -/
theorem written_bounds {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536 := by
  have mask := (NativeBranchDecoderProofs.decoded_fields fields query).mask
  rw [(NativeBranchFieldProofs.dummy_port holds mask).2]
  decide

/-- Proved local preservation includes both readonly refreshes and the actual
    destination write. No expected value or preservation rule is supplied. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily)
    {entry : BranchProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : Trace.Proofs.RowWriteBoundsFromReads row := by
  cases row with
  | mk family w =>
    cases family
    intro port member reads
    change port ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · rw [Trace.Proofs.write_word]
      change (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536
      exact written_bounds native fields query

end Airbender.ReducedMachine.NativeBranchPreservationProofs
