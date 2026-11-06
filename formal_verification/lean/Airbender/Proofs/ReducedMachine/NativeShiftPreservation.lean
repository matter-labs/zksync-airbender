import Airbender.Proofs.ReducedMachine.NativeShiftBounded
import Airbender.Proofs.ReducedMachine.NativeShiftDecoder
import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Proofs.Trace.Values

namespace Airbender.ReducedMachine.NativeShiftPreservationProofs
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

/-- The actual masked port write preserves ranges, using only the earlier source read internally. -/
theorem written_bounds {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (source : (source1 w)[0].val < 65536 ∧ (source1 w)[1].val < 65536) :
    (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536 := by
  have decoded := NativeShiftDecoderProofs.decoded_fields fields query
  obtain ⟨useRegister,mask⟩ := decoded.mask
  have bounds := NativeShiftBoundedProofs.candidate_bounds holds entry.data.family useRegister mask source
  have candidate := NativeShiftWriteProofs.candidate holds entry.data.family useRegister mask
  have write := NativeShiftWriteProofs.write holds entry.data.family useRegister mask
  have actual : rdWrite w = (#v[w 116,w 117]).map (fun value => (1 - rdZeroFlag w) * value) :=
    write.trans (congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 =>
      v.map (fun value => (1 - rdZeroFlag w) * value)) candidate).symm
  have bit : rdZeroFlag w = 0 ∨ rdZeroFlag w = 1 := by
    rw [decoded.zero]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have limbs : ∀ i : Fin 2, (#v[w 116,w 117])[i].val < 65536 := by
    intro i
    fin_cases i
    · exact bounds.1
    · exact bounds.2
  rw [actual]
  exact ⟨masked_bounds _ _ bit limbs 0,masked_bounds _ _ bit limbs 1⟩

/-- A proved local induction rule: readonly refreshes preserve exact reads and
    the third write depends on the earlier first read plus decoded native effects. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily) {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
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
    · have first := reads importedConstraintsMemoryPorts[0]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (by
          change (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 0 ≤
            (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 2
          omega)
      rw [Trace.Proofs.read_word] at first
      change (source1 w)[0].val < 65536 ∧ (source1 w)[1].val < 65536 at first
      rw [Trace.Proofs.write_word]
      change (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536
      exact written_bounds native fields query first

end Airbender.ReducedMachine.NativeShiftPreservationProofs
