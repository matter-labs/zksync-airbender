module
public import Slop.KeccakSplit.Reference.Chain
public import Slop.KeccakSplit.Reference.Permutation
public import Human.Trace.Workers.Keccak.Permutation

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Specs.Keccak256
set_option warningAsError true

/-- The physical slot of Clean lane `lane` in the initial row-major layout. -/
def initialSlot (lane : Fin 25) : Fin 31 :=
  ⟨Controller.physicalLane 0 lane, Nat.lt_trans (Controller.Proofs.physical_bound 0 lane) (by decide)⟩

theorem initial_slot_bound (lane : Fin 25) : (initialSlot lane).val < 30 :=
  Nat.lt_trans (Controller.Proofs.physical_bound 0 lane) (by decide)

/-- The low word of Clean lane `lane` sits at its public lane offset. -/
theorem low_lane_cell (pointer : BitVec 32) (lane : Fin 25) :
    laneCell pointer (initialSlot lane) false =
      .ram (pointer + BitVec.ofNat 32 (Keccak.Permutation.laneOffset lane)) := by
  simp only [laneCell, initialSlot, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Keccak.Permutation.laneOffset, Controller.physicalLane]

/-- The high word of Clean lane `lane` sits four bytes above its public lane offset. -/
theorem high_lane_cell (pointer : BitVec 32) (lane : Fin 25) :
    laneCell pointer (initialSlot lane) true =
      .ram (pointer + BitVec.ofNat 32 (Keccak.Permutation.laneOffset lane) + 4) := by
  simp only [laneCell, initialSlot, ↓reduceIte, Keccak.Permutation.laneOffset,
    Controller.physicalLane]
  rw [BitVec.add_assoc, BitVec.ofNat_add]
  rfl

end Airbender.Keccak.Split.Call.Proofs
