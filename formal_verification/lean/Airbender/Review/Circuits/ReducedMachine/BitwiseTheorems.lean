import Airbender.Proofs.ReducedMachine.NativeBitwiseResult

namespace Airbender.ReducedMachine.Native
open Arithmetic Verification
set_option autoImplicit false

/-- Actual native byte queries force complete RV32 bitwise candidates and all
    input/output word bounds. Original public decoding/history is composed later. -/
theorem bitwise_result {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (kind : BinaryKind) (useRegister : Bool)
    (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) :
    (sourceWord w).Bounded ∧ (operandWord w).Bounded ∧ (candidateWord w).Bounded ∧
      (candidateWord w).toBitVec = byteOperation kind.tag (sourceWord w).toBitVec (operandWord w).toBitVec :=
  NativeBitwiseResultProofs.candidate_result holds kind useRegister mask tag

/-- Actual native destination address and field-masked port write. Original
    decoder rd/x0 and selected register/immediate identity remain explicit boundaries. -/
theorem bitwise_masked_write {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
      rdWrite w = (arithmeticCandidate w).map (fun value => (1 - rdZeroFlag w) * value) :=
  NativeBitwiseFieldProofs.write holds useRegister mask

end Airbender.ReducedMachine.Native
