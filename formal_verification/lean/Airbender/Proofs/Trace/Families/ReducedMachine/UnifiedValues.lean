import Airbender.Proofs.ReducedMachine.NativeUnifiedLocal
import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedDecoder
import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowImage

namespace Airbender.ReducedMachine.NativeUnifiedRangeProofs
open Native Trace NativeShadow
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original public decoding derives every local native write-preservation rule. -/
theorem decoded_write_rules {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup) :
    WriteBoundsFromReads (fixedData trace) := by
  intro row present
  obtain ⟨entry,member,source,query⟩ := NativeUnifiedDecoderProofs.trace_decoding image accepted decoded row present
  cases row with
  | mk family w =>
    cases family
    have canonical := native_query_pc_word (by decide : Arithmetic.limbBase < mersenne31Modulus) query
    change initialPCWord w = Arithmetic.Word.ofBitVec entry.pc at canonical
    have aligned : (initialPCWord w).lo % 4 = 0 := by
      rw [canonical]
      exact (run_sparse_setup_sources image member).2
    exact NativeUnifiedLocalProofs.row_write_rule _ (accepted.constraints _ present) source.fields query aligned

/-- Shared time induction derives every native read/write/terminal bound from
    public seeds and proved native write rules, never from a supplied source range. -/
theorem image_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds) (accepted : Accepted (fixedData trace))
    (decoded : UnifiedDecodedTrace (fixedData trace) setup) :
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ (fixedData trace).terminalMemory, token.word.Bounded) := by
  have clocks := NativeShadowProofs.shadow_clock_boundary (by decide) inputs
  have seedBounds := NativeShadowProofs.shadow_image_bounds inputs
  have rules := decoded_write_rules image accepted decoded
  exact ⟨read_bounds_of_rules (by decide) accepted clocks seedBounds rules,
    write_bounds_of_rules (by decide) accepted clocks seedBounds rules,
    terminal_bounds_of_rules (by decide) accepted clocks seedBounds rules⟩

end Airbender.ReducedMachine.NativeUnifiedRangeProofs
