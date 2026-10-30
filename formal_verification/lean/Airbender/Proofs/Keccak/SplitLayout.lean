import Airbender.Proofs.Keccak.SplitPermutationDefinitions

namespace Airbender.Keccak.Split.Call.Proofs
set_option warningAsError true

/-- Convert the original Clean lane coordinate to the split row-major coordinate. -/
def transposeLane (lane : Fin 25) : Fin 25 :=
  ⟨lane.val / 5 + 5 * (lane.val % 5), by
    have := lane.isLt
    have := Nat.mod_lt lane.val (by decide : 0 < 5)
    omega⟩

/-- Both public coordinate conventions select the same inverse Pi source. -/
theorem transpose_pi_source : ∀ lane : Fin 25,
    piSource (transposeLane lane) = transposeLane (Controller.piSource lane) := by
  decide +kernel

/-- Physical slots agree with the original Clean lane layout after every Pi. -/
theorem physical_slot_reference (round : Nat) (lane : Fin 25) :
    (physicalSlot round (transposeLane lane)).val = Controller.physicalLane round lane := by
  induction round generalizing lane with
  | zero => rfl
  | succ round ih =>
    simp only [physicalSlot, Controller.physicalLane]
    rw [transpose_pi_source]
    exact ih _

end Airbender.Keccak.Split.Call.Proofs
