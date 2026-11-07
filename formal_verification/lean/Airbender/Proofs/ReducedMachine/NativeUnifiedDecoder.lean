import Airbender.Review.Circuits.ReducedMachine.UnifiedDecoder
import Airbender.Proofs.ReducedMachine.NativeSupportedDecoder
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDecoder

namespace Airbender.ReducedMachine.NativeUnifiedDecoderProofs
open Native Trace Arithmetic
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original projection selects the checked interface, retaining exact PC/bits/
    instruction/data/ten-field query. No expected per-row profile is supplied. -/
theorem entry_profile {entry : UnifiedProgramEntry}
    (fields : unifiedDecoderFields entry.instruction = some entry.data) :
    (∃ selected : SupportedProgramEntry, selected.pc = entry.pc ∧ selected.bits = entry.bits ∧
      selected.instruction = entry.instruction ∧ supportedDecoderFields selected.instruction = some selected.data ∧
      entry.data = selected.data.mapFamily Sum.inl ∧ selected.query (p := mersenne31Modulus) = entry.query) ∨
    (∃ selected : WordMemoryProgramEntry, selected.pc = entry.pc ∧ selected.bits = entry.bits ∧
      selected.instruction = entry.instruction ∧ wordMemoryDecoderFields selected.instruction = some selected.data ∧
      entry.data = selected.data.mapFamily Sum.inr ∧ selected.query (p := mersenne31Modulus) = entry.query) := by
  unfold unifiedDecoderFields at fields
  cases supported : supportedDecoderFields entry.instruction with
  | some data =>
    simp only [supported] at fields
    have same := Option.some.inj fields
    refine Or.inl ⟨⟨entry.pc,entry.bits,entry.instruction,data⟩,rfl,rfl,rfl,supported,same.symm,?_⟩
    unfold ProgramEntry.query
    rw [← same]
    rfl
  | none =>
    simp only [supported] at fields
    cases memory : wordMemoryDecoderFields entry.instruction with
    | none => simp [memory] at fields
    | some data =>
      simp only [memory,Option.map_some] at fields
      have same := Option.some.inj fields
      refine Or.inr ⟨⟨entry.pc,entry.bits,entry.instruction,data⟩,rfl,rfl,rfl,memory,same.symm,?_⟩
      unfold ProgramEntry.query
      rw [← same]
      rfl

/-- Native eighteen-bit packing excludes holes/tail in complete original public
    membership; no supplied exclusion or table identity is used. -/
theorem fetched_sources {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before unifiedDecoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry,present,same⟩ := sparse_member member (NativeShiftDecoderProofs.padding_excluded holds)
  exact ⟨entry,present,(run_sparse_setup_sources image present).1,same⟩

end Airbender.ReducedMachine.NativeUnifiedDecoderProofs
