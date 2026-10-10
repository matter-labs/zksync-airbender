import Airbender.Proofs.Keccak.RhoOperations

namespace Airbender.Keccak.Proofs.Rho
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def rhoLimbs {p : Nat} (w : Nat → ZMod p) (operation : Fin 5) : Vector Nat 4 :=
  (readLaneLimbs w ⟨operation.val, by omega⟩).map ZMod.val

theorem rho_limbs_at {p : Nat} (w : Nat → ZMod p) (operation : Fin 5) (limb : Fin 4) :
    (rhoLimbs w operation)[limb] = (w (15 + 8 * operation.val + limbOffset[limb])).val := by
  fin_cases limb <;> simp [rhoLimbs, readLaneLimbs, limbOffset, Nat.add_comm] <;> congr 2 <;> omega

theorem rho_packed {p : Nat} (w : Nat → ZMod p) (operation : Fin 5) :
    packLane (rhoLimbs w operation) = readLane w ⟨operation.val, by omega⟩ := by
  simp only [packLane]
  change (rhoLimbs w operation)[(0 : Fin 4)] +
    65536 * ((rhoLimbs w operation)[(1 : Fin 4)] +
      65536 * ((rhoLimbs w operation)[(2 : Fin 4)] +
        65536 * (rhoLimbs w operation)[(3 : Fin 4)])) = _
  rw [rho_limbs_at, rho_limbs_at, rho_limbs_at, rho_limbs_at]
  rfl

theorem rho_rotated_limb {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (column : Fin 5)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1) (selected : w 67 = 1)
    (iterations : ∀ i : Fin 5, w Variables.iterationColumns[i] = if i = column then 1 else 0)
    (operation : Fin 5) (bounds : ∀ i : Fin 4, (rhoLimbs w operation)[i] < 65536)
    (limb : Fin 4) :
    (w (17 + 8 * operation.val + limbOffset[limb])).val =
      rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] limb := by
  let left := rotations[column][operation]
  have key (i : Fin 4) : (w (102 + 24 * operation.val + i.val)).val =
      (rhoLimbs w operation)[i] + 65536 * (left.val % 16) := by
    have route := (rho_routes (by omega) column h active selected iterations operation i).1
    have natural : w (102 + 24 * operation.val + i.val) =
        (((rhoLimbs w operation)[i] + 65536 * (left.val % 16) : Nat) : ZMod p) := by
      rw [rho_limbs_at]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using route
    rw [natural, ZMod.val_natCast_of_lt (by
      have := bounds i; have : left.val % 16 < 16 := Nat.mod_lt _ (by decide); omega)]
  have parts (i : Fin 4) :
      (w (110 + 24 * operation.val + i.val)).val =
        (rhoLimbs w operation)[i] / 2 ^ (16 - left.val % 16) ∧
      (w (118 + 24 * operation.val + i.val)).val =
        ((rhoLimbs w operation)[i] * 2 ^ (left.val % 16)) % 65536 := by
    have facts := rho_rotation_parts hp h active selected operation i
    rw [key i] at facts
    have bound := bounds i
    have remainder : ((rhoLimbs w operation)[i] + 65536 * (left.val % 16)) % 65536 =
        (rhoLimbs w operation)[i] := by omega
    have quotient : ((rhoLimbs w operation)[i] + 65536 * (left.val % 16)) / 65536 =
        left.val % 16 := by omega
    simpa only [remainder, quotient] using facts.2.2.2
  let source := rotationSource left limb
  have current := parts source
  have prior := parts (rotationPrevious source)
  have route := (rho_routes (by omega) column h active selected iterations operation limb).2
  have natural : (((w (118 + 24 * operation.val + source.val)).val +
      (w (110 + 24 * operation.val + (rotationPrevious source).val)).val : Nat) : ZMod p) =
      w (17 + 8 * operation.val + limbOffset[limb]) := by
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using route
  have small : (w (118 + 24 * operation.val + source.val)).val +
      (w (110 + 24 * operation.val + (rotationPrevious source).val)).val < p := by
    rw [current.2, prior.1]
    exact lt_of_lt_of_le (rotated_lane_limb_bound bounds left limb) (by omega)
  have value := congrArg ZMod.val natural
  rw [ZMod.val_natCast_of_lt small] at value
  exact value.symm.trans (by rw [current.2, prior.1]; rfl)

theorem rho_rotated_lane {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (column : Fin 5)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1) (selected : w 67 = 1)
    (iterations : ∀ i : Fin 5, w Variables.iterationColumns[i] = if i = column then 1 else 0)
    (operation : Fin 5) (bounds : ∀ i : Fin 4, (rhoLimbs w operation)[i] < 65536) :
    writeLane w ⟨operation.val, by omega⟩ =
      rotLeft64 (readLane w ⟨operation.val, by omega⟩) rotations[column][operation] := by
  have result := rotate_left_of_limbs bounds rotations[column][operation]
  rw [rho_packed] at result
  simp only [packLane, Vector.getElem_map, Vector.getElem_finRange] at result
  change rotLeft64 (readLane w ⟨operation.val, by omega⟩) _ =
    rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (0 : Fin 4) +
      65536 * (rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (1 : Fin 4) +
        65536 * (rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (2 : Fin 4) +
          65536 * rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (3 : Fin 4))) at result
  have l0 := rho_rotated_limb hp column h active selected iterations operation bounds (0 : Fin 4)
  have l1 := rho_rotated_limb hp column h active selected iterations operation bounds (1 : Fin 4)
  have l2 := rho_rotated_limb hp column h active selected iterations operation bounds (2 : Fin 4)
  have l3 := rho_rotated_limb hp column h active selected iterations operation bounds (3 : Fin 4)
  change (w (17 + 8 * operation.val)).val =
    rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (0 : Fin 4) at l0
  change (w (17 + 8 * operation.val + 1)).val =
    rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (1 : Fin 4) at l1
  change (w (17 + 8 * operation.val + 4)).val =
    rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (2 : Fin 4) at l2
  change (w (17 + 8 * operation.val + 5)).val =
    rotatedLaneLimb (rhoLimbs w operation) rotations[column][operation] (3 : Fin 4) at l3
  change laneValue w (17 + 8 * operation.val) = rotLeft64 (laneValue w (15 + 8 * operation.val)) _
  simp only [laneValue]
  rw [l0, l1, l2, l3]
  exact result.symm

end Airbender.Keccak.Proofs.Rho
