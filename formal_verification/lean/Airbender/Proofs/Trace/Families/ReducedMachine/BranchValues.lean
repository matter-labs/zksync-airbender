import Airbender.Proofs.ReducedMachine.NativeBranchPreservation
import Airbender.Proofs.Trace.Families.ReducedMachine.BranchDecoder
import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Review.Trace.Families.ReducedMachine.FixedData

namespace Airbender.ReducedMachine.NativeBranchRangeProofs
open Native Trace
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original public decoding derives every local native write-preservation rule. -/
theorem decoded_write_rules {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : branchDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : BranchDecodedTrace (fixedData trace) setup) :
    WriteBoundsFromReads (fixedData trace) := by
  intro row present
  obtain ⟨entry,_,source,query,_⟩ := NativeBranchDecoderProofs.trace_decoding image accepted decoded row present
  cases row with
  | mk family w =>
    cases family
    exact NativeBranchPreservationProofs.row_write_rule _ (accepted.constraints _ present) source.fields query

/-- Shared time induction derives every native read/write/terminal bound from
    public seeds and proved native write rules, never from a supplied source range. -/
theorem image_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : branchDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : BranchDecodedTrace (fixedData trace) setup) :
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ (fixedData trace).terminalMemory, token.word.Bounded) := by
  have clocks := image_clock_boundary (by decide) inputs
  have seeds := image_bounds inputs.image
  have rules := decoded_write_rules image accepted decoded
  exact ⟨read_bounds_of_rules (by decide) accepted clocks seeds rules,
    write_bounds_of_rules (by decide) accepted clocks seeds rules,
    terminal_bounds_of_rules (by decide) accepted clocks seeds rules⟩

end Airbender.ReducedMachine.NativeBranchRangeProofs
