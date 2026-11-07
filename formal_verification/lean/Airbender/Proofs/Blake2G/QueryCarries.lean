import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.FrameCarries

namespace Airbender.Blake2G.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- A bounded sum of two limbs and one incoming bit cannot carry twice. The
    statement concerns field values and is independent of native storage. -/
theorem two_input_carry_bound {p a b output incoming : Nat} [Fact p.Prime]
    (hp : FieldCapacity.AtLeast p 262144) {carry : ZMod p}
    (ha : a < 65536) (hb : b < 65536) (ho : output < 65536)
    (hi : incoming ≤ 1) (hc : carry.val < 3)
    (equation : (a : ZMod p) + b + incoming = output + 65536 * carry) :
    carry.val ≤ 1 := by
  have cast : ((a + b + incoming : Nat) : ZMod p) =
      ((output + 65536 * carry.val : Nat) : ZMod p) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      ZMod.natCast_zmod_val] using equation
  have lifted := congrArg ZMod.val cast
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at lifted
  omega

theorem boolean_of_value_le_one {p : Nat} [Fact p.Prime] {value : ZMod p}
    (bound : value.val ≤ 1) : value = 0 ∨ value = 1 := by
  have cases : value.val = 0 ∨ value.val = 1 := by omega
  rcases cases with zero | one
  · left
    rw [← ZMod.natCast_zmod_val value, zero, Nat.cast_zero]
  · right
    rw [← ZMod.natCast_zmod_val value, one, Nat.cast_one]

/-- Query-only G bounds discharge the final two carry flags. This avoids a
    circular dependence on the full fragment's Boolean assertions. -/
theorem second_c_carries_of_queries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 262144)
    (compatible : SerializedInverse.Scale64 p)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (queries : QueryHolds (setupTable control) w)
    (carries : (w 75).val < 3 ∧ (w 76).val < 3) :
    (w 75 = 0 ∨ w 75 = 1) ∧ (w 76 = 0 ∨ w 76 = 1) := by
  have firstC := (first_rotation12_of_queries (by omega) compatible queries).2.1
  have rotatedD := (second_rotation_of_queries (by omega) compatible queries).2.1
  have secondC := (second_rotation7_of_queries (by omega) compatible queries).1
  have low := two_input_carry_bound hp firstC.1 rotatedD.1 secondC.1
    (incoming := 0) (by omega) carries.1 (by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
        ZMod.natCast_zmod_val]
      unfold secondClo
      ring)
  have high := two_input_carry_bound hp firstC.2 rotatedD.2 secondC.2
    low carries.2 (by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      unfold secondChi
      ring)
  exact ⟨boolean_of_value_le_one low, boolean_of_value_le_one high⟩

/-- One shared certificate discharges all carry flags for a query-projected
    frame, including layouts which encode the final carries inside lookups. -/
theorem Frame.flags_from_queries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 262144)
    (compatible : SerializedInverse.Scale64 p) (frame : Frame p)
    (control : Fin 512 → Vector Nat 7) (queries : QueryHolds (setupTable control) frame.assignment)
    (addition : ∀ slot : Fin 4, frame.addCarries[slot].val < 3)
    (firstC : ∀ slot : Fin 2,
      frame.cCarries[(slot.castLE (by decide) : Fin 4)] = 0 ∨ frame.cCarries[(slot.castLE (by decide) : Fin 4)] = 1)
    (lastC : ∀ slot : Fin 2, frame.cCarries[(⟨2 + slot.val, by omega⟩ : Fin 4)].val < 3)
    (k : Fin 12) :
    frame.base Variables.booleanColumns[1 + k.val] = 0 ∨
      frame.base Variables.booleanColumns[1 + k.val] = 1 := by
  have bounds : (frame.assignment 75).val < 3 ∧ (frame.assignment 76).val < 3 := by
    simpa [Frame.assignment, assemble, Frame.base] using And.intro (lastC 0) (lastC 1)
  have finalC := second_c_carries_of_queries hp compatible queries bounds
  apply frame.flags_of_bounds addition
  intro slot
  fin_cases slot
  · exact firstC 0
  · exact firstC 1
  · simpa [Frame.assignment, assemble, Frame.base] using finalC.1
  · simpa [Frame.assignment, assemble, Frame.base] using finalC.2

end Airbender.Blake2G.Proofs
