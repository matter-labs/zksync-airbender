import Airbender.Proofs.ShiftBinop.Decoder

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native routing is assembled from the actual accepted selector/tag/operand equations. -/
theorem selected_routing {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (op : Operation) (immediate : Bool)
    (mask : w 12 = ((op.mask + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (op.funct3 : ZMod mersenne31Modulus)) :
    (∀ slot : Fin 4, w (42 + 4 * slot.val) = (op.lookupTags[slot.val] : ZMod mersenne31Modulus)) ∧
    w 27 = (if immediate then w 9 else w 25) ∧
    w 28 = (if immediate then w 10 else w 26) ∧ w 37 = 0 := by
  obtain ⟨sll, srl, sra, binary, csr, useImm⟩ := selected_bits holds op immediate mask
  have e0 := assertion_of_holds holds ⟨13, by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨14, by rw [constraint_count]; decide⟩
  have e2 := assertion_of_holds holds ⟨16, by rw [constraint_count]; decide⟩
  have e3 := assertion_of_holds holds ⟨24, by rw [constraint_count]; decide⟩
  have e4 := assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  have e5 := assertion_of_holds holds ⟨32, by rw [constraint_count]; decide⟩
  have e6 := assertion_of_holds holds ⟨36, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at e0 e1 e2 e3 e4 e5 e6
  cases op <;> cases immediate
  all_goals
    simp only [Operation.funct3] at tag
    simp only [Operation.isBinary, reduceCtorEq, if_true, if_false] at sll srl sra binary useImm
    simp only [sll, srl, sra, binary, csr, useImm, tag, zero_mul, one_mul,
      mul_zero, mul_one, zero_add, add_zero] at e0 e1 e2 e3 e4 e5 e6
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro slot
      fin_cases slot <;> simp [Operation.lookupTags]
      all_goals first | linear_combination -e3 | linear_combination -e4 |
        linear_combination -e5 | linear_combination -e6
    · dsimp
      linear_combination -e0
    · dsimp
      linear_combination -e1
    · linear_combination -e2

/-- Original public decoding supplies mask and funct3; routing is a conclusion. -/
theorem entry_routing {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : Routing w entry := by
  obtain ⟨_, immediate, mask, tag⟩ := decoder_field_bounds fields
  have maskQuery := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at maskQuery
  have tagQuery := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) query
  change w 11 = (entry.data.funct3 : ZMod mersenne31Modulus) at tagQuery
  have routed := selected_routing holds entry.data.family immediate (by rw [maskQuery, mask]) (by rw [tagQuery, tag])
  have selected : (32 ≤ entry.data.mask) ↔ immediate = true := by
    rw [mask]
    cases entry.data.family <;> cases immediate <;> decide
  exact ⟨routed.1, by simpa only [selected] using routed.2.1,
    by simpa only [selected] using routed.2.2.1, routed.2.2.2⟩

/-- No selected-result or operation-bit premise: original public construction
    and native membership recover the decoded entry and its routing. -/
theorem fetched_routing {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      decoderQuery w = entry.query ∧ Routing w entry := by
  obtain ⟨entry, present, source, same⟩ := fetched_sources image holds member
  exact ⟨entry, present, source, same, entry_routing holds source.fields same⟩

end Airbender.ShiftBinop.Proofs
