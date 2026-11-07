import Airbender.Proofs.Trace.Families.ReducedMachine.BranchResults

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public initialization/full original decoding and native fixed-pool acceptance
    derive actual branch conditions, canonical target/final PC, RV32 wrap and
    successor alignment. No source/range/condition/target/PC/state answer is given.
    Original Sail GPR/clauses/fetched execution and physical setup remain separate. -/
theorem public_branch_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : branchDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : BranchDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before branchDecoderFields ∧
      row.decoderQuery = entry.query ∧ BranchDecoded row.assignment entry ∧ BranchNumericalEffects row.assignment :=
  NativeBranchRangeProofs.image_branch_results image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
