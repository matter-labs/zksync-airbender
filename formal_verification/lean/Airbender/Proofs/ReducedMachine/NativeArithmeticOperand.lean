import Airbender.Proofs.ReducedMachine.NativeArithmeticDecoder
import Airbender.Proofs.ReducedMachine.NativeArithmeticFields
import Airbender.Review.Circuits.ReducedMachine.ShiftOperand

namespace Airbender.ReducedMachine.NativeArithmeticOperandProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native selected arithmetic operands retain readonly rs2 participation on
    immediate forms. Original decoded bounds canonically recover the immediate. -/
theorem entry_selected_operand {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ArithmeticProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : arithmeticDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    operandWord w = if entry.data.family.useRegister then registerOperandWord w else entry.data.immediate := by
  have decoded := NativeArithmeticDecoderProofs.decoded_fields fields query
  have routed := NativeArithmeticFieldProofs.source native entry.data.family decoded.mask
  have word := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => (⟨v[0].val,v[1].val⟩ : Word)) routed
  have actual : operandWord w = if entry.data.family.useRegister then registerOperandWord w else arithmeticImmediateWord w := by
    cases choice : entry.data.family.useRegister <;>
      simpa [choice,operandWord,registerOperandWord,arithmeticImmediateWord,
        importedConstraintsMemoryPorts,Trace.WordColumns.evaluate] using word
  rw [actual,NativeArithmeticDecoderProofs.immediate_word fields query]

end Airbender.ReducedMachine.NativeArithmeticOperandProofs
