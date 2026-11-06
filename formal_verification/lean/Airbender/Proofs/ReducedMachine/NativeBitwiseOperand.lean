import Airbender.Proofs.ReducedMachine.NativeBitwiseDecoder
import Airbender.Proofs.ReducedMachine.NativeBitwiseFields
import Airbender.Review.Circuits.ReducedMachine.ShiftOperand

namespace Airbender.ReducedMachine.NativeBitwiseOperandProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native selected bitwise operands retain readonly rs2 participation on
    immediate forms. Original decoded bounds canonically recover the immediate. -/
theorem entry_selected_operand {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BitwiseProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : bitwiseDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    operandWord w = if entry.data.family.useRegister then registerOperandWord w else entry.data.immediate := by
  have decoded := NativeBitwiseDecoderProofs.decoded_fields fields query
  have routed := NativeBitwiseFieldProofs.source native entry.data.family.useRegister decoded.mask
  have word := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => (⟨v[0].val,v[1].val⟩ : Word)) routed
  have actual : operandWord w = if entry.data.family.useRegister then registerOperandWord w else arithmeticImmediateWord w := by
    cases choice : entry.data.family.useRegister <;>
      simpa [choice,operandWord,registerOperandWord,arithmeticImmediateWord,
        importedConstraintsMemoryPorts,Trace.WordColumns.evaluate] using word
  rw [actual,NativeBitwiseDecoderProofs.immediate_word fields query]

end Airbender.ReducedMachine.NativeBitwiseOperandProofs
