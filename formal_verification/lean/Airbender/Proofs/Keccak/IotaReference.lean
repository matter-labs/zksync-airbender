import Airbender.Review.Circuits.Keccak.Tables.Operations
import Mathlib.Tactic.FinCases

namespace Airbender.Keccak.Proofs.IotaReference
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/- A kernel-checked normal form of the unchanged reference, used only for
   proof calculation. Actual circuit lookup contents remain imported data. -/
private def bytes : Vector Nat 256 := #v[
  0, 1, 130, 138, 0, 139, 1, 129, 9, 138, 136, 9, 10, 139, 139, 137,
  3, 2, 128, 10, 10, 129, 128, 1, 8, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 128, 128, 128, 128, 0, 128, 128, 0, 0, 128, 0, 128, 0, 128,
  128, 128, 0, 128, 0, 128, 128, 0, 128, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 128, 0, 128, 128, 0, 0, 0, 128, 128, 128, 0, 0,
  0, 0, 0, 0, 128, 128, 0, 128, 128, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 128, 128, 0, 0, 128, 128, 0, 0, 0, 0, 0, 128, 128,
  128, 128, 128, 0, 128, 128, 128, 0, 128, 0, 0, 0, 0, 0, 0, 0]

private theorem all_bytes : ∀ key : Fin 256, bytes[key] = iotaByte key.val := by
  have blocks : ∀ block : Fin 16, ∀ offset : Fin 16,
      bytes[16 * block.val + offset.val]'(by omega) =
        iotaByte (16 * block.val + offset.val) := by
    intro block
    fin_cases block <;>
      dsimp only [bytes, Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray] <;>
      decide +kernel
  intro key
  have value := blocks ⟨key.val / 16, by omega⟩ ⟨key.val % 16, Nat.mod_lt _ (by decide)⟩
  simpa only [Fin.getElem_fin,
    show 16 * (key.val / 16) + key.val % 16 = key.val by omega] using value

def byte (control : Nat) : Nat :=
  if h : control < 256 then bytes[control]'h else iotaByte control

/-- Reference normalization is exact for every control, including controls
    outside the byte-key domain. -/
theorem byte_eq (control : Nat) : byte control = iotaByte control := by
  unfold byte
  split_ifs with bound
  · exact all_bytes ⟨control, bound⟩
  · rfl

end Airbender.Keccak.Proofs.IotaReference
