import Airbender.Proofs.Keccak.MixRoutes
import Airbender.Proofs.Keccak.ByteLookupValues
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Keccak.Mix
import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Proofs.Keccak.FixedLookups
import Airbender.Proofs.Arithmetic.ByteAssembly

namespace Airbender.Keccak.Proofs.Mix
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem mix_xor_bytes {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (xor : isRotation second operation = false) (byte : Fin 8) :
    (w (102 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (110 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val =
      (w (102 + 24 * operation.val + byte.val)).val ^^^
        (w (110 + 24 * operation.val + byte.val)).val := by
  have query := ByteQueryBindings.values hp h operation byte
  have tags := selected_tags (by omega) h active (mixMode second) selected
    ⟨8 * operation.val + byte.val, by omega⟩
  have group : (⟨(8 * operation.val + byte.val) / 8, by omega⟩ : Fin 5) = operation := by
    apply Fin.ext
    change (8 * operation.val + byte.val) / 8 = operation.val
    omega
  have indexEq := congrArg (fun i : Fin 5 => operationTags[mixMode second][i]) group
  have selectedTag : (byteTag (setupTable control) w
      ⟨8 * operation.val + byte.val, by omega⟩).val = operationTags[mixMode second][operation] :=
    tags.trans indexEq
  have tagKind : operationTags[mixMode second][operation] = 4 := by
    cases second <;> fin_cases operation <;> simp [isRotation, mixMode, operationTags] at xor ⊢
  rw [selectedTag, tagKind] at query
  simpa [ByteOperationFacts] using query


theorem mix_xor_limb {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (xor : isRotation second operation = false) (limb : Fin 4) :
    (w (aColumns second)[operation][limb]).val < 65536 ∧
    (w (bColumns second)[operation][limb]).val < 65536 ∧
    (w (cColumns second)[operation][limb]).val < 65536 ∧
    (w (cColumns second)[operation][limb]).val =
      (w (aColumns second)[operation][limb]).val ^^^
        (w (bColumns second)[operation][limb]).val := by
  have low := mix_xor_bytes hp second h active selected operation xor ⟨2 * limb.val, by omega⟩
  have high := mix_xor_bytes hp second h active selected operation xor ⟨2 * limb.val + 1, by omega⟩
  have routes := mix_routes (by omega) second h active selected operation limb
  simp only [xor, Bool.false_eq_true, if_false] at routes
  have ia : 103 + 24 * operation.val + 2 * limb.val =
      102 + 24 * operation.val + (2 * limb.val + 1) := by omega
  have ib : 111 + 24 * operation.val + 2 * limb.val =
      110 + 24 * operation.val + (2 * limb.val + 1) := by omega
  have ic : 119 + 24 * operation.val + 2 * limb.val =
      118 + 24 * operation.val + (2 * limb.val + 1) := by omega
  rw [ia, ib, ic] at routes
  have a := value_of_bounded_pair (radix := 256) (capacity := 256) (by omega) low.1 high.1 routes.1
  have b := value_of_bounded_pair (radix := 256) (capacity := 256) (by omega) low.2.1 high.2.1 routes.2.1
  have c := value_of_bounded_pair (radix := 256) (capacity := 256) (by omega) low.2.2.1 high.2.2.1 routes.2.2
  refine ⟨by rw [a]; omega, by rw [b]; omega, by rw [c]; omega, ?_⟩
  rw [a, b, c, low.2.2.2, high.2.2.2]
  have value := xor_of_chunks (width := 8) low.1 low.2.1
    (a₁ := (w (102 + 24 * operation.val + (2 * limb.val + 1))).val)
    (b₁ := (w (110 + 24 * operation.val + (2 * limb.val + 1))).val)
  norm_num only [Nat.reducePow] at value
  exact value.symm

theorem mix_xor_operation {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (xor : isRotation second operation = false) :
    packed w (cColumns second)[operation] =
      packed w (aColumns second)[operation] ^^^ packed w (bColumns second)[operation] := by
  have l0 := mix_xor_limb hp second h active selected operation xor (0 : Fin 4)
  have l1 := mix_xor_limb hp second h active selected operation xor (1 : Fin 4)
  have l2 := mix_xor_limb hp second h active selected operation xor (2 : Fin 4)
  have l3 := mix_xor_limb hp second h active selected operation xor (3 : Fin 4)
  simp [packed] at l0 l1 l2 l3 ⊢
  rw [l0.2.2.2, l1.2.2.2, l2.2.2.2, l3.2.2.2]
  have value := xor_of_four_chunks (width := 16) l0.1 l1.1 l2.1 l0.2.1 l1.2.1 l2.2.1
    (a₃ := (w (aColumns second)[operation][3]).val)
    (b₃ := (w (bColumns second)[operation][3]).val)
  norm_num only [Nat.reducePow] at value
  exact value.symm

end Airbender.Keccak.Proofs.Mix
