import Airbender.Proofs.ShiftBinop.Routing
import Airbender.Review.Circuits.ShiftBinop.BinaryModel
import Airbender.Review.Circuits.ShiftBinop.Lookups
import Airbender.Review.Helpers.Tables.NativeBinary

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original decoded masks and funct3 select the actual four native byte tables. -/
theorem binary_queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : BinaryKind) (immediate : Bool)
    (mask : w 12 = ((8 + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) (slot : Fin 4) :
    NativeBinary.Contains kind #v[w (39 + 4 * slot.val), w (40 + 4 * slot.val), w (41 + 4 * slot.val)] := by
  have selected := selected_routing holds (binaryOperation kind) immediate
    (by cases kind <;> exact mask) (by cases kind <;> exact tag)
  have tags : w (42 + 4 * slot.val) = (kind.tag : ZMod mersenne31Modulus) := by
    have chosen := selected.1 slot
    cases kind <;> fin_cases slot <;> exact chosen
  apply (native_lookup_binary kind _).mp
  change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[]
    #v[w (39 + 4 * slot.val), w (40 + 4 * slot.val), w (41 + 4 * slot.val), (kind.tag : ZMod mersenne31Modulus)]
  simpa only [tags] using native_lookup_queries holds slot

/-- Byte bounds and bitwise values are conclusions of accepted original queries. -/
theorem binary_bytes {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : BinaryKind) (immediate : Bool)
    (mask : w 12 = ((8 + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) (slot : Fin 4) :
    (w (39 + 4 * slot.val)).val < 256 ∧ (w (40 + 4 * slot.val)).val < 256 ∧
    (w (41 + 4 * slot.val)).val < 256 ∧
    BitVec.ofNat 8 (w (41 + 4 * slot.val)).val = byteOperation kind.tag
      (BitVec.ofNat 8 (w (39 + 4 * slot.val)).val)
      (BitVec.ofNat 8 (w (40 + 4 * slot.val)).val) :=
  native_binary_result kind _ (binary_queries holds kind immediate mask tag slot)

/-- Native inverse-256 equations reconstruct the actual input limbs and selected
    output from the four byte queries; no operand bounds are assumed. -/
theorem binary_pairs {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (immediate : Bool)
    (mask : w 12 = ((8 + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus)) :
    w 39 + 256 * w 43 = w 23 ∧ w 47 + 256 * w 51 = w 24 ∧
    w 40 + 256 * w 44 = w 27 ∧ w 48 + 256 * w 52 = w 28 ∧
    w 41 + 256 * w 45 = w 55 ∧ w 49 + 256 * w 53 = w 56 := by
  obtain ⟨sll,srl,sra,binary,csr,_⟩ := selected_bits holds .xor immediate mask
  simp only [Operation.isBinary,reduceCtorEq,if_true,if_false] at sll srl sra binary
  have e21 := assertion_of_holds holds ⟨21, by rw [constraint_count]; decide⟩
  have e22 := assertion_of_holds holds ⟨22, by rw [constraint_count]; decide⟩
  have e23 := assertion_of_holds holds ⟨23, by rw [constraint_count]; decide⟩
  have e25 := assertion_of_holds holds ⟨25, by rw [constraint_count]; decide⟩
  have e26 := assertion_of_holds holds ⟨26, by rw [constraint_count]; decide⟩
  have e27 := assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  have e29 := assertion_of_holds holds ⟨29, by rw [constraint_count]; decide⟩
  have e30 := assertion_of_holds holds ⟨30, by rw [constraint_count]; decide⟩
  have e31 := assertion_of_holds holds ⟨31, by rw [constraint_count]; decide⟩
  have e33 := assertion_of_holds holds ⟨33, by rw [constraint_count]; decide⟩
  have e34 := assertion_of_holds holds ⟨34, by rw [constraint_count]; decide⟩
  have e35 := assertion_of_holds holds ⟨35, by rw [constraint_count]; decide⟩
  have e37 := assertion_of_holds holds ⟨37, by rw [constraint_count]; decide⟩
  have e38 := assertion_of_holds holds ⟨38, by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    sll,srl,sra,binary,csr] at e21 e22 e23 e25 e26 e27 e29 e30 e31 e33 e34 e35 e37 e38
  have modulus : (2147483647 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linear_combination (norm := (ring_nf; simp only [modulus,mul_zero,neg_zero,add_zero])) -256 * e25 - e21
  · linear_combination (norm := (ring_nf; simp only [modulus,mul_zero,neg_zero,add_zero])) -256 * e33 - e29
  · linear_combination (norm := (ring_nf; simp only [modulus,mul_zero,neg_zero,add_zero])) -256 * e26 - e22
  · linear_combination (norm := (ring_nf; simp only [modulus,mul_zero,neg_zero,add_zero])) -256 * e34 - e30
  · linear_combination e37 - e23 - 256 * e27
  · linear_combination e38 - e31 - 256 * e35

end Airbender.ShiftBinop.Proofs
