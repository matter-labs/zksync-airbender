import Airbender.Review.Circuits.ReducedMachine.ShiftOperand
import Airbender.Proofs.ReducedMachine.NativeShiftDecoder
import Airbender.Proofs.ReducedMachine.NativeShiftRouting

namespace Airbender.ReducedMachine.NativeShiftOperandProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original supported constructors determine the native register/immediate bit. -/
theorem form_mask {instruction : SailRV32.instruction} {data : Trace.DecoderData ShiftMode}
    (fields : shiftDecoderFields instruction = some data) :
    data.mask = data.family.mask (shiftUsesRegister instruction) := by
  unfold shiftDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [Native.shiftFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       rfl)

/-- Actual selected fields equal the original decoded register/immediate operand.
    The readonly rs2 word is retained even when the selected operand is immediate. -/
theorem entry_selected_operand {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    operandWord w = if shiftUsesRegister entry.instruction then registerOperandWord w else entry.data.immediate := by
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  rw [form_mask fields] at packed
  have routed := NativeShiftRoutingProofs.source native entry.data.family (shiftUsesRegister entry.instruction) packed
  have word := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => (⟨v[0].val,v[1].val⟩ : Word)) routed
  have decoded := NativeShiftDecoderProofs.decoded_fields fields query
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) decoded.immediate
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) decoded.immediate
  change w 9 = (entry.data.immediate.lo : ZMod mersenne31Modulus) at low
  change w 10 = (entry.data.immediate.hi : ZMod mersenne31Modulus) at high
  have bounds := (NativeShiftDecoderProofs.field_bounds fields).1
  have small : limbBase < mersenne31Modulus := by decide
  cases form : shiftUsesRegister entry.instruction
  · simp only [form,Bool.false_eq_true,if_false] at word ⊢
    have selected : operandWord w = ⟨(w 9).val,(w 10).val⟩ := word
    rw [selected]
    apply congrArg₂ Word.mk
    · rw [low,ZMod.val_natCast_of_lt (lt_trans bounds.1 small)]
    · rw [high,ZMod.val_natCast_of_lt (lt_trans bounds.2 small)]
  · simpa [form,operandWord,registerOperandWord,importedConstraintsMemoryPorts,Trace.WordColumns.evaluate] using word

end Airbender.ReducedMachine.NativeShiftOperandProofs
