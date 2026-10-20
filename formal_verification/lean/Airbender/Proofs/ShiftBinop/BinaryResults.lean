import Airbender.Proofs.ShiftBinop.BinaryValues

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual native destination columns discard exactly the decoded x0 write. -/
theorem written_mask {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (discarded : Bool) (zeroFlag : w 8 = if discarded then 1 else 0) :
    writtenWord w = if discarded then ⟨0,0⟩ else selectedWord w := by
  have e0 := assertion_of_holds holds ⟨39,by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨40,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0 e1
  have lo : w 59 = if discarded then 0 else w 55 := by
    cases discarded <;> simp only [Bool.false_eq_true,if_false,if_true] at zeroFlag ⊢ <;>
      rw [zeroFlag] at e0 <;> linear_combination -e0
  have hi : w 60 = if discarded then 0 else w 56 := by
    cases discarded <;> simp only [Bool.false_eq_true,if_false,if_true] at zeroFlag ⊢ <;>
      rw [zeroFlag] at e1 <;> linear_combination -e1
  cases discarded <;> simp only [Bool.false_eq_true,if_false,if_true] at lo hi ⊢
  all_goals
    apply congrArg₂ Word.mk
    · simpa using congrArg ZMod.val lo
    · simpa using congrArg ZMod.val hi

/-- The decoded entry supplies the mask, tag and x0 flag; the native row supplies
    the exact selected result and all input/output limb bounds. -/
theorem entry_binary_result {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (kind : BinaryKind)
    (family : entry.data.family = binaryOperation kind) :
    BinaryResult w kind (decide (entry.data.rd = 0)) := by
  obtain ⟨_,immediate,mask,tag⟩ := decoder_field_bounds fields
  have maskQuery := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at maskQuery
  have tagQuery := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) query
  change w 11 = (entry.data.funct3 : ZMod mersenne31Modulus) at tagQuery
  have nativeMask : w 12 = ((8 + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus) := by
    rw [maskQuery,mask,family]
    cases kind <;> rfl
  have nativeTag : w 11 = (kind.tag : ZMod mersenne31Modulus) := by
    rw [tagQuery,tag,family]
    cases kind <;> rfl
  have zeroFlag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
  change w 8 = (if entry.data.rd = 0 then 1 else 0) at zeroFlag
  obtain ⟨leftBound,rightBound,selectedBound,result⟩ := binary_selected holds kind immediate nativeMask nativeTag
  exact ⟨leftBound,rightBound,selectedBound,result,
    written_mask holds _ (by simpa only [decide_eq_true_eq] using zeroFlag)⟩

/-- Original public bytes and native membership recover the operation; no
    selector, table-equivalence, operand bound or desired-result premise. -/
theorem fetched_binary_result {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      decoderQuery w = entry.query ∧ Routing w entry ∧
      ∀ kind, entry.data.family = binaryOperation kind →
        BinaryResult w kind (decide (entry.data.rd = 0)) := by
  obtain ⟨entry,present,source,query,routing⟩ := fetched_routing image holds member
  exact ⟨entry,present,source,query,routing,fun kind family =>
    entry_binary_result holds source.fields query kind family⟩

end Airbender.ShiftBinop.Proofs
