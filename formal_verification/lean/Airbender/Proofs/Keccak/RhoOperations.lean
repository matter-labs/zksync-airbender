import Airbender.Proofs.Keccak.RhoRoutes
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Keccak.Rho
import Airbender.Proofs.Arithmetic.LaneRotation

import Airbender.Proofs.Keccak.ByteLookupValues

namespace Airbender.Keccak.Proofs.Rho
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4800000

theorem rho_rotation_parts {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1) (selected : w 67 = 1)
    (operation : Fin 5) (limb : Fin 4) :
    (w (102 + 24 * operation.val + limb.val)).val < 1048576 ∧
    (w (110 + 24 * operation.val + limb.val)).val < 65536 ∧
    (w (118 + 24 * operation.val + limb.val)).val < 65536 ∧
    (w (110 + 24 * operation.val + limb.val)).val =
      ((w (102 + 24 * operation.val + limb.val)).val % 65536) /
        2 ^ (16 - (w (102 + 24 * operation.val + limb.val)).val / 65536) ∧
    (w (118 + 24 * operation.val + limb.val)).val =
      (((w (102 + 24 * operation.val + limb.val)).val % 65536) *
        2 ^ ((w (102 + 24 * operation.val + limb.val)).val / 65536)) % 65536 := by
  have query := ByteQueryBindings.values hp h operation (limb.castLE (by decide))
  simp only [Fin.val_castLE] at query
  have tags := selected_tags (by omega) h active (4 : Fin 7) selected
    ⟨8 * operation.val + limb.val, by omega⟩
  have group : (⟨(8 * operation.val + limb.val) / 8, by omega⟩ : Fin 5) = operation := by
    apply Fin.ext
    change (8 * operation.val + limb.val) / 8 = operation.val
    omega
  have indexEq := congrArg (fun i : Fin 5 => operationTags[(4 : Fin 7)][i]) group
  have selectedTag : (byteTag (setupTable control) w
      ⟨8 * operation.val + limb.val, by omega⟩).val = operationTags[(4 : Fin 7)][operation] :=
    tags.trans indexEq
  have tagKind : operationTags[(4 : Fin 7)][operation] = 40 := by
    fin_cases operation <;> rfl
  rw [selectedTag, tagKind] at query
  simpa [ByteOperationFacts] using query

end Airbender.Keccak.Proofs.Rho
