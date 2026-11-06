import Slop.KeccakSplit.Reference.Chain
import Slop.KeccakSplit.Reference.Permutation
import Human.Trace.Workers.Keccak.Permutation

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Specs.Keccak256
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

/-- A physical snapshot exposes Clean's round-zero lanes at the public lane offsets. -/
theorem lanes_at_of_snapshot {state : State} {pointer : BitVec 32} {lanes : LaneState}
    (snapshot : PhysicalSnapshot state pointer lanes) :
    Keccak.Permutation.LanesAt state pointer (logicalLanes 0 lanes) := by
  intro lane
  have observed := snapshot.2 (initialSlot lane) (initial_slot_bound lane)
  have value : (logicalLanes 0 lanes)[lane] = lanes (initialSlot lane) := by
    simp only [logicalLanes, Fin.getElem_fin, Vector.getElem_ofFn, initialSlot]
  refine ⟨half (lanes (initialSlot lane)) false, half (lanes (initialSlot lane)) true,
    ?_, ?_, ?_, ?_⟩
  · rw [← low_lane_cell]
    exact observed.2 false
  · rw [← high_lane_cell]
    exact observed.2 true
  · rw [value]
    have bound := observed.1
    simp only [half, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    have upper : lanes (initialSlot lane) / 2 ^ 32 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt upper]
    omega
  · rw [value]
    exact observed.1

/-- The 361 documented split calls, executed in Sail from successful reads of the
x11 pointer and of the thirty physical lanes, write Clean's Keccak-f[1600]
permutation of the initial state block. -/
theorem permutation_of_executions (states : Fin 362 → State) (pointer : BitVec 32)
    (exec : ∀ index : Fin 361, ExecutesAt index (states index.castSucc) (states index.succ))
    (pointerRead : (Cell.register 11).read (states 0) = .ok pointer (states 0))
    (initialReads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (laneCell pointer ⟨slot.val, by omega⟩ high).read (states 0) = .ok value (states 0)) :
    ∃ input output : Vector Nat 25,
      Keccak.Permutation.WordMapping (states 0) (states 361) pointer input output ∧
      output = keccakPermutation input := by
  obtain ⟨_, lanes, _, snapshots, steps⟩ :=
    chain_of_executions states pointer exec pointerRead initialReads
  refine ⟨logicalLanes 0 (lanes 0), logicalLanes 0 (lanes 361),
    ⟨pointerRead, lanes_at_of_snapshot (snapshots 0), lanes_at_of_snapshot (snapshots 361)⟩, ?_⟩
  exact permutation_of_physical_chain lanes fun index => steps index

end Airbender.Keccak.Split.Call.Proofs
