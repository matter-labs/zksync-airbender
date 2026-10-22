import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.Keccak.Addresses
import Airbender.Proofs.Keccak.Controller
import Airbender.Proofs.ScaledMemoryPorts

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

theorem addresses {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (rowsBounded : ∀ key : Fin 4096, ∀ i : Fin 6, (control key)[i] < 31)
    (pointerBounded : (statePointer w).Bounded)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : AddressChecks w := by
  have align := pointer_alignment hp inverse h
  obtain ⟨key, _, selected⟩ := controller_indices (by omega) rowsBounded h
  have indices (i : Fin 6) : (w (7 + i.val)).val < 31 := by
    rw [selected i]
    exact rowsBounded key i
  have noCarry (i : Fin 12) : (statePointer w).lo +
      8 * (w (7 + i.val / 2)).val + 4 * (i.val % 2) < limbBase := by
    have indexBound : (w (7 + i.val / 2)).val < 31 := indices ⟨i.val / 2, by omega⟩
    have inside : 8 * (w (7 + i.val / 2)).val + 4 * (i.val % 2) < 256 := by omega
    simpa only [Nat.add_assoc] using Verification.block_offset_bound (block := 256)
      (low := (statePointer w).lo) (by decide) pointerBounded.1 align inside
  refine ⟨align, indices, noCarry, ?_⟩
  intro i
  have layout := congrArg (fun (ports : Vector Verification.IndirectPort 12) => ports[i]) port_layout
  rw [layout]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  change (Verification.IndirectPort.mk 11 i.val #v[13, 14] 8
    (some (7 + i.val / 2)) (4 * (i.val % 2))
    #v[15 + 4 * i.val, 16 + 4 * i.val]
    (some #v[17 + 4 * i.val, 18 + 4 * i.val])).address w = _
  exact Verification.IndirectPort.scaled_address (by omega) rfl rfl rfl (noCarry i)

end Airbender.Keccak.Proofs
