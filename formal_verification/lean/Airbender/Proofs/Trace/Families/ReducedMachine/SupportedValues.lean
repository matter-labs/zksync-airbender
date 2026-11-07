import Airbender.Proofs.ReducedMachine.NativeSupportedLocal
import Airbender.Proofs.Trace.Families.ReducedMachine.SupportedDecoder
import Airbender.Proofs.Trace.Families.ReducedMachine.History

namespace Airbender.ReducedMachine.NativeSupportedRangeProofs
open Native Trace
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original public decoding derives every local native write-preservation rule. -/
theorem decoded_write_rules {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : SupportedDecodedTrace (fixedData trace) setup) :
    WriteBoundsFromReads (fixedData trace) := by
  intro row present
  obtain ⟨entry,member,source,query⟩ := NativeSupportedDecoderProofs.trace_decoding image accepted decoded row present
  cases row with
  | mk family w =>
    cases family
    have canonical := native_query_pc_word (by decide : Arithmetic.limbBase < mersenne31Modulus) query
    change initialPCWord w = Arithmetic.Word.ofBitVec entry.pc at canonical
    have aligned : (initialPCWord w).lo % 4 = 0 := by
      rw [canonical]
      exact (run_sparse_setup_sources image member).2
    exact NativeSupportedLocalProofs.row_write_rule _ (accepted.constraints _ present) source.fields query aligned

/-- Shared time induction derives every native read/write/terminal bound from
    public seeds and proved native write rules, never from a supplied source range. -/
theorem image_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : supportedDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : SupportedDecodedTrace (fixedData trace) setup) :
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

end Airbender.ReducedMachine.NativeSupportedRangeProofs
