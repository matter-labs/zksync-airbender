import Airbender.Proofs.ReducedMachine.NativeCSRDecoder
import Airbender.Proofs.ReducedMachine.NativeCSRResult
import Airbender.Proofs.ReducedMachine.NativeCSRFields
import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Proofs.Trace.Values

namespace Airbender.ReducedMachine.NativeCSRPreservationProofs
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

/-- Actual scalar oracle lookups and original decoded rd/x0 fields derive
    actual bounded writes without any source/read bound premise. -/
theorem written_bounds {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536 := by
  have decoded := NativeCSRDecoderProofs.decoded_fields fields query
  have bounds := NativeCSRResultProofs.oracle_bounds holds
  have candidate := NativeCSRFieldProofs.candidate holds decoded.mask
  have write := (NativeCSRFieldProofs.write holds decoded.mask).2
  have bit : rdZeroFlag w = 0 ∨ rdZeroFlag w = 1 := by
    rw [decoded.zero]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have limbs : ∀ i : Fin 2, (csrCandidate w)[i].val < 65536 := by
    intro i
    fin_cases i
    · simpa [candidate,csrOracleWord,Arithmetic.limbBase] using bounds.1
    · simpa [candidate,csrOracleWord,Arithmetic.limbBase] using bounds.2
  rw [write]
  exact ⟨masked_bounds _ _ bit limbs 0,masked_bounds _ _ bit limbs 1⟩

/-- Proved local preservation includes both readonly refreshes and the actual
    destination write. No expected value or preservation rule is supplied. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily)
    {fixed : Table (ZMod mersenne31Modulus) (fields 4)} {entry : CSRProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints fixed))
    (fields : csrDecoderFields entry.instruction = some entry.data)
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

end Airbender.ReducedMachine.NativeCSRPreservationProofs
