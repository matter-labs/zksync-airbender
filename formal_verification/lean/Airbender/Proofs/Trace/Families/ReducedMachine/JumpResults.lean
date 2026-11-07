import Airbender.Proofs.Trace.Families.ReducedMachine.JumpValues
import Airbender.Proofs.ReducedMachine.NativeJumpDecodedResult

namespace Airbender.ReducedMachine.NativeJumpRangeProofs
open Native Trace Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Public initialization/full original decoding discharges the internal
    source/PC/offset/alignment/parity inputs before actual jump numerical results. -/
theorem image_jump_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup JumpMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : jumpDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : JumpDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before jumpDecoderFields ∧
      row.decoderQuery = entry.query ∧ JumpDecoded row.assignment entry ∧ JumpNumericalEffects row.assignment entry := by
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  obtain ⟨entry,found,source,query,fields⟩ := NativeJumpDecoderProofs.trace_decoding image accepted decoded row present
  refine ⟨entry,found,source,query,fields,?_⟩
  cases row with
  | mk family w =>
    cases family
    have first := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at first
    have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
    change initialPCWord w = Word.ofBitVec entry.pc at canonical
    have aligned : (initialPCWord w).lo % 4 = 0 := by
      rw [canonical]
      exact (Trace.Proofs.run_sparse_setup_sources image found).2
    exact NativeJumpResultProofs.decoded_result (accepted.constraints _ present) source query first aligned

end Airbender.ReducedMachine.NativeJumpRangeProofs
