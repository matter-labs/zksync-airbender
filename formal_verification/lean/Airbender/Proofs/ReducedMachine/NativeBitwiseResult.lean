import Airbender.Proofs.ReducedMachine.NativeBitwiseFields
import Airbender.Proofs.ReducedMachine.NativeBitwiseTable
import Airbender.Proofs.ShiftBinop.BinaryValues

namespace Airbender.ReducedMachine.NativeBitwiseResultProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact actual native byte meanings and all three byte ranges. No operand,
    byte or output range is supplied to the theorem. -/
theorem bytes {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (kind : BinaryKind) (useRegister : Bool)
    (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) (slot : Fin 4) :
    ((bitwiseBytes w)[slot][0]).val < 256 ∧ ((bitwiseBytes w)[slot][1]).val < 256 ∧
      ((bitwiseBytes w)[slot][2]).val < 256 ∧
      BitVec.ofNat 8 ((bitwiseBytes w)[slot][2]).val = byteOperation kind.tag
        (BitVec.ofNat 8 ((bitwiseBytes w)[slot][0]).val)
        (BitVec.ofNat 8 ((bitwiseBytes w)[slot][1]).val) := by
  have member := NativeBitwiseFieldProofs.queries holds useRegister mask slot
  rw [tag] at member
  have actual := NativeBitwiseTableProofs.result kind _ member (by simp)
  simpa using actual

/-- Canonical source/selected operand/candidate limb reconstruction follows
    from the actual native inverse-256 equations and the proved byte ranges. -/
theorem pair_values {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (kind : BinaryKind) (useRegister : Bool)
    (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) :
    (w 35).val = (w 55).val + 256 * (w 104).val ∧
    (w 36).val = (w 108).val + 256 * (w 57).val ∧
    (w 47).val = (w 58).val + 256 * (w 105).val ∧
    (w 48).val = (w 109).val + 256 * (w 60).val ∧
    (w 116).val = (w 64).val + 256 * (w 65).val ∧
    (w 117).val = (w 66).val + 256 * (w 67).val := by
  obtain ⟨_,loA,loB,hiA,hiB⟩ := NativeBitwiseFieldProofs.query_fields holds useRegister mask
  obtain ⟨loC,hiC⟩ := NativeBitwiseFieldProofs.candidate holds useRegister mask
  have b0 := bytes holds kind useRegister mask tag 0
  have b1 := bytes holds kind useRegister mask tag 1
  have b2 := bytes holds kind useRegister mask tag 2
  have b3 := bytes holds kind useRegister mask tag 3
  exact ⟨byte_pair_value (by decide) _ _ _ b0.1 b1.1 loA.symm,
    byte_pair_value (by decide) _ _ _ b2.1 b3.1 hiA.symm,
    byte_pair_value (by decide) _ _ _ b0.2.1 b1.2.1 loB.symm,
    byte_pair_value (by decide) _ _ _ b2.2.1 b3.2.1 hiB.symm,
    byte_pair_value (by decide) _ _ _ b0.2.2.1 b1.2.2.1 loC.symm,
    byte_pair_value (by decide) _ _ _ b2.2.2.1 b3.2.2.1 hiC.symm⟩

/-- Complete canonical RV32 result at the actual native candidate columns.
    Pure byte/word packing is reused only after new native query connections. -/
theorem candidate_result {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (kind : BinaryKind) (useRegister : Bool)
    (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) :
    (sourceWord w).Bounded ∧ (operandWord w).Bounded ∧ (candidateWord w).Bounded ∧
      (candidateWord w).toBitVec = byteOperation kind.tag (sourceWord w).toBitVec (operandWord w).toBitVec := by
  obtain ⟨loA,hiA,loB,hiB,loC,hiC⟩ := pair_values holds kind useRegister mask tag
  have values := bytes holds kind useRegister mask tag
  have a := ShiftBinop.Proofs.word_of_byte_pairs (word := sourceWord w)
    (fun i => ((bitwiseBytes w)[i][0]).val) (fun i => (values i).1) loA hiA
  have b := ShiftBinop.Proofs.word_of_byte_pairs (word := operandWord w)
    (fun i => ((bitwiseBytes w)[i][1]).val) (fun i => (values i).2.1) loB hiB
  have c := ShiftBinop.Proofs.word_of_byte_pairs (word := candidateWord w)
    (fun i => ((bitwiseBytes w)[i][2]).val) (fun i => (values i).2.2.1) loC hiC
  refine ⟨a.1,b.1,c.1,?_⟩
  rw [a.2,b.2,ShiftBinop.Proofs.binary_pack,c.2]
  congr 1
  funext i
  exact (values i).2.2.2

end Airbender.ReducedMachine.NativeBitwiseResultProofs
