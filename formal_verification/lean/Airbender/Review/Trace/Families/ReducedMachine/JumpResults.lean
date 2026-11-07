import Airbender.Proofs.Trace.Families.ReducedMachine.JumpResults

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public initialization/full original decoding and native fixed-pool acceptance
    derive canonical return/candidate/write, raw/selected target, RV32 wrap and
    successor alignment. No source/range/condition/target/PC/state answer is given.
    Original Sail GPR/clauses/fetched execution and physical setup remain separate. -/
theorem public_jump_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup JumpMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : jumpDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : JumpDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before jumpDecoderFields ∧
      row.decoderQuery = entry.query ∧ JumpDecoded row.assignment entry ∧ JumpNumericalEffects row.assignment entry :=
  NativeJumpRangeProofs.image_jump_results image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
