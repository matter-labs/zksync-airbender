import Airbender.Proofs.ReducedMachine.NativeComparisonDecoder
import Airbender.Proofs.ReducedMachine.NativeComparisonResult
import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Proofs.Trace.Values

namespace Airbender.ReducedMachine.NativeComparisonPreservationProofs
open Native Trace Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem masked_bounds (v : Vector (ZMod mersenne31Modulus) 2)
    (flag : ZMod mersenne31Modulus) (bit : flag = 0 ∨ flag = 1)
    (bounds : ∀ i : Fin 2, v[i].val < 65536) (i : Fin 2) :
    (v.map (fun value => (1 - flag) * value))[i].val < 65536 := by
  rcases bit with zero | one
  · simpa [zero] using bounds i
  · simp [one]

/-- Actual resolver lookup and original decoded mask/tag/rd/x0 fields derive
    actual bounded writes without any source/read bound premise. -/
theorem written_bounds {w : Nat → ZMod mersenne31Modulus} {entry : ComparisonProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : comparisonDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536 := by
  have decoded := NativeComparisonDecoderProofs.decoded_fields fields query
  have bounds := NativeComparisonResultProofs.candidate_bounds holds entry.data.family.useRegister
    entry.data.family.signed decoded.mask (by simpa [ComparisonMode.tag] using decoded.funct3)
  have write := (NativeComparisonFieldProofs.write holds entry.data.family.useRegister decoded.mask).2
  have bit : rdZeroFlag w = 0 ∨ rdZeroFlag w = 1 := by
    rw [decoded.zero]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have limbs : ∀ i : Fin 2, (arithmeticCandidate w)[i].val < 65536 := by
    intro i
    fin_cases i
    · exact bounds.1
    · exact bounds.2
  rw [write]
  exact ⟨masked_bounds _ _ bit limbs 0,masked_bounds _ _ bit limbs 1⟩

/-- Proved local preservation includes both readonly refreshes and the actual
    destination write. No expected value or preservation rule is supplied. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily)
    {entry : ComparisonProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : comparisonDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : Trace.Proofs.RowWriteBoundsFromReads row := by
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
      exact written_bounds native fields query

end Airbender.ReducedMachine.NativeComparisonPreservationProofs
