module
public import Proven.Keccak.MixOperations
public import Proven.Arithmetic.RotationAssembly
public import Proven.Defs.Circuits.Keccak.Artifact
public import Proven.Defs.Circuits.Keccak.Tables.Setup

@[expose] public section

namespace Airbender.Keccak.Proofs.Mix
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem mix_rotation_parts {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (rotation : isRotation second operation = true) (limb : Fin 4) :
    (w (102 + 24 * operation.val + limb.val)).val < 1048576 ∧
    (w (110 + 24 * operation.val + limb.val)).val < 65536 ∧
    (w (118 + 24 * operation.val + limb.val)).val < 65536 ∧
    (w (110 + 24 * operation.val + limb.val)).val =
      ((w (102 + 24 * operation.val + limb.val)).val % 65536) /
        2 ^ (16 - (w (102 + 24 * operation.val + limb.val)).val / 65536) ∧
    (w (118 + 24 * operation.val + limb.val)).val =
      (((w (102 + 24 * operation.val + limb.val)).val % 65536) *
        2 ^ ((w (102 + 24 * operation.val + limb.val)).val / 65536)) % 65536 := by
  have tag : operationTags[mixMode second][operation.val] = 40 := by
    cases second <;> fin_cases operation <;> first | rfl | simp [isRotation] at rotation
  have facts := selected_byte_facts hp h active (mixMode second) selected operation ⟨limb.val, by omega⟩
  rw [tag] at facts
  exact rotation_byte_facts facts

theorem mix_rotated_limb {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (rotation : isRotation second operation = true)
    (bounds : ∀ i : Fin 4, (w (aColumns second)[operation][i]).val < 65536)
    (limb : Fin 4) :
    (w (cColumns second)[operation][limb]).val =
      (2 * (w (aColumns second)[operation][limb]).val) % 65536 +
        (w (aColumns second)[operation][previous limb]).val / 32768 := by
  have key (i : Fin 4) : (w (102 + 24 * operation.val + i.val)).val =
      (w (aColumns second)[operation][i]).val + 65536 := by
    have routes := mix_routes (by omega) second h active selected operation i
    simp only [rotation, ite_true] at routes
    have natural : w (102 + 24 * operation.val + i.val) =
        (((w (aColumns second)[operation][i]).val + 65536 : Nat) : ZMod p) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val] using routes.1
    rw [natural, ZMod.val_natCast_of_lt (by have := bounds i; omega)]
  have parts (i : Fin 4) :
      (w (110 + 24 * operation.val + i.val)).val = (w (aColumns second)[operation][i]).val / 32768 ∧
      (w (118 + 24 * operation.val + i.val)).val = (2 * (w (aColumns second)[operation][i]).val) % 65536 := by
    have facts := mix_rotation_parts hp second h active selected operation rotation i
    have small := bounds i
    rw [key i] at facts
    have remainder : ((w (aColumns second)[operation][i]).val + 65536) % 65536 =
        (w (aColumns second)[operation][i]).val := by omega
    have quotient : ((w (aColumns second)[operation][i]).val + 65536) / 65536 = 1 := by omega
    simpa only [remainder, quotient, Nat.reduceSub, Nat.reducePow, mul_comm] using facts.2.2.2
  have current := parts limb
  have prior := parts (previous limb)
  have sourceBound := bounds limb
  have priorBound := bounds (previous limb)
  have routes := mix_routes (by omega) second h active selected operation limb
  simp only [rotation, ite_true] at routes
  have natural : (((w (118 + 24 * operation.val + limb.val)).val +
      (w (110 + 24 * operation.val + (previous limb).val)).val : Nat) : ZMod p) =
      w (cColumns second)[operation][limb] := by
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using routes.2
  have small : (w (118 + 24 * operation.val + limb.val)).val +
      (w (110 + 24 * operation.val + (previous limb).val)).val < p := by
    rw [current.2, prior.1]
    omega
  have value := congrArg ZMod.val natural
  rw [ZMod.val_natCast_of_lt small] at value
  exact value.symm.trans (by rw [current.2, prior.1])

theorem mix_rotation_operation {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (rotation : isRotation second operation = true)
    (bounds : ∀ i : Fin 4, (w (aColumns second)[operation][i]).val < 65536) :
    packed w (cColumns second)[operation] = rotLeft64 (packed w (aColumns second)[operation]) 1 := by
  have l0 := mix_rotated_limb hp second h active selected operation rotation bounds (0 : Fin 4)
  have l1 := mix_rotated_limb hp second h active selected operation rotation bounds (1 : Fin 4)
  have l2 := mix_rotated_limb hp second h active selected operation rotation bounds (2 : Fin 4)
  have l3 := mix_rotated_limb hp second h active selected operation rotation bounds (3 : Fin 4)
  change (w (cColumns second)[operation][0]).val =
    2 * (w (aColumns second)[operation][0]).val % 65536 + (w (aColumns second)[operation][3]).val / 32768 at l0
  change (w (cColumns second)[operation][1]).val =
    2 * (w (aColumns second)[operation][1]).val % 65536 + (w (aColumns second)[operation][0]).val / 32768 at l1
  change (w (cColumns second)[operation][2]).val =
    2 * (w (aColumns second)[operation][2]).val % 65536 + (w (aColumns second)[operation][1]).val / 32768 at l2
  change (w (cColumns second)[operation][3]).val =
    2 * (w (aColumns second)[operation][3]).val % 65536 + (w (aColumns second)[operation][2]).val / 32768 at l3
  simp only [packed]
  rw [l0, l1, l2, l3]
  exact (rotate_left_one_of_limbs (bounds 0) (bounds 1) (bounds 2)).symm

end Airbender.Keccak.Proofs.Mix
