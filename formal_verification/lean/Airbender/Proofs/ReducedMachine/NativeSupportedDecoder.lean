import Airbender.Review.Circuits.ReducedMachine.SupportedDecoder
import Airbender.Proofs.ReducedMachine.NativeArithmeticDecoder

namespace Airbender.ReducedMachine.NativeSupportedDecoderProofs
open Native Trace Arithmetic
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The original projection, not a supplied per-row profile, selects one of the
    previously checked native local interfaces. Mapping changes no query field. -/
theorem entry_profile {entry : SupportedProgramEntry}
    (fields : supportedDecoderFields entry.instruction = some entry.data) :
    (∃ selected : ShiftProgramEntry, selected.instruction = entry.instruction ∧
      shiftDecoderFields selected.instruction = some selected.data ∧
      selected.query (p := mersenne31Modulus) = entry.query) ∨
    (∃ selected : ArithmeticProgramEntry, selected.instruction = entry.instruction ∧
      arithmeticDecoderFields selected.instruction = some selected.data ∧
      selected.query (p := mersenne31Modulus) = entry.query) := by
  unfold supportedDecoderFields at fields
  cases shift : shiftDecoderFields entry.instruction with
  | some data =>
    simp only [shift] at fields
    have same := Option.some.inj fields
    refine Or.inl ⟨⟨entry.pc,entry.bits,entry.instruction,data⟩,rfl,shift,?_⟩
    unfold ProgramEntry.query
    rw [← same]
    rfl
  | none =>
    simp only [shift] at fields
    cases arithmetic : arithmeticDecoderFields entry.instruction with
    | none => simp [arithmetic] at fields
    | some data =>
      simp only [arithmetic,Option.map_some] at fields
      have same := Option.some.inj fields
      refine Or.inr ⟨⟨entry.pc,entry.bits,entry.instruction,data⟩,rfl,arithmetic,?_⟩
      unfold ProgramEntry.query
      rw [← same]
      rfl

/-- Full original public decoding and actual eighteen-bit packing recover the
    entry and exclude unsupported holes/padding without a supplied exclusion. -/
theorem fetched_sources {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup SupportedMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : supportedDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before supportedDecoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry,present,same⟩ := sparse_member member (NativeShiftDecoderProofs.padding_excluded holds)
  exact ⟨entry,present,(run_sparse_setup_sources image present).1,same⟩

end Airbender.ReducedMachine.NativeSupportedDecoderProofs
