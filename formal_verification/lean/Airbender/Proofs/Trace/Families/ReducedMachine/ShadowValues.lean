import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryResults
import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowImage

namespace Airbender.ReducedMachine.NativeShadowRangeProofs
open Native Trace NativeShadow Arithmetic
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Shared time induction derives every native read/write/terminal bound from
    public seeds and proved native write rules, never from a supplied source range. -/
theorem image_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds) (accepted : Accepted (fixedData trace))
    (decoded : WordMemoryDecodedTrace (fixedData trace) setup) :
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ (fixedData trace).terminalMemory, token.word.Bounded) := by
  have clocks := NativeShadowProofs.shadow_clock_boundary (by decide) inputs
  have bounds := NativeShadowProofs.shadow_image_bounds inputs
  have rules := NativeWordMemoryRangeProofs.decoded_write_rules image accepted decoded
  exact ⟨read_bounds_of_rules (by decide) accepted clocks bounds rules,
    write_bounds_of_rules (by decide) accepted clocks bounds rules,
    terminal_bounds_of_rules (by decide) accepted clocks bounds rules⟩


/-- Public initialized ranges and original source membership discharge all
    internal address-addition/read/PC inputs. These native words are not yet
    original pre-row Sail GPR/architectural memory observations. -/
theorem image_word_memory_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds) (accepted : Accepted (fixedData trace))
    (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before wordMemoryDecoderFields ∧
      row.decoderQuery = entry.query ∧ WordMemoryDecoded row.assignment entry ∧
      WordMemoryNumericalEffects row.assignment entry := by
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  obtain ⟨entry,found,source,query,fields⟩ := NativeWordMemoryDecoderProofs.trace_decoding image accepted decoded row present
  refine ⟨entry,found,source,query,fields,?_⟩
  cases row with
  | mk family w =>
    cases family
    have first := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at first
    change (sourceWord w).Bounded at first
    have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
    change initialPCWord w = Word.ofBitVec entry.pc at canonical
    have aligned : (initialPCWord w).lo%4 = 0 := by
      rw [canonical]
      exact (Trace.Proofs.run_sparse_setup_sources image found).2
    exact NativeWordMemoryResultProofs.decoded_result (accepted.constraints _ present) source.fields query first aligned

end Airbender.ReducedMachine.NativeShadowRangeProofs
