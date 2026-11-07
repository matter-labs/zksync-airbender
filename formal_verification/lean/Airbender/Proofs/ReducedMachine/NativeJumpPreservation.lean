import Airbender.Proofs.ReducedMachine.NativeJumpDecoder
import Airbender.Proofs.ReducedMachine.NativeJumpReturn
import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Proofs.Trace.Values

namespace Airbender.ReducedMachine.NativeJumpPreservationProofs
open Native Trace Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Return preservation follows canonical public PC inputs, not source ranges. -/
theorem written_bounds {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536 := by
  have result := (NativeJumpReturnProofs.candidate_result holds fields query aligned).2
  have bound : (writtenWord w).Bounded := by
    rw [result]
    split
    · constructor <;> decide
    · exact Word.ofBitVec_bound _
  exact bound

/-- Proved local preservation includes both readonly refreshes and the actual
    destination write. No expected value or preservation rule is supplied. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily)
    {entry : JumpProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query)
    (aligned : (initialPCWord row.assignment).lo % 4 = 0) : Trace.Proofs.RowWriteBoundsFromReads row := by
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
      exact written_bounds native fields query aligned

end Airbender.ReducedMachine.NativeJumpPreservationProofs
