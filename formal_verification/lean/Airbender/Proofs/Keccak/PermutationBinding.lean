import Airbender.Proofs.Keccak.CallPermutation
import Airbender.Review.Trace.Workers.Keccak.Permutation

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private theorem lanes_at {state : State} {pointer : BitVec 32} {cells : List Cell}
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read state = .ok value state) :
    Permutation.LanesAt state pointer (logicalLanes 0 (physicalLanes state pointer)) := by
  intro lane
  let physical : Fin 31 := ⟨Controller.physicalLane 0 lane,
    Nat.lt_trans (Controller.Proofs.physical_bound 0 lane) (by decide)⟩
  obtain ⟨low, lowRead⟩ := readable _ (tracked physical 0)
  obtain ⟨high, highRead⟩ := readable _ (tracked physical 1)
  have lowRead : (Cell.ram (pointer + BitVec.ofNat 32 (Permutation.laneOffset lane))).read state =
      .ok low state := by
    simpa only [physical, Controller.physicalLane, Permutation.laneOffset, Fin.val_zero,
      Nat.mul_zero, Nat.add_zero] using lowRead
  have four : BitVec.ofNat 32 4 = (4 : BitVec 32) := by decide +kernel
  have highRead : (Cell.ram (pointer + BitVec.ofNat 32 (Permutation.laneOffset lane) + 4)).read state =
      .ok high state := by
    simpa only [physical, Controller.physicalLane, Permutation.laneOffset, Fin.val_one,
      Nat.mul_one, BitVec.ofNat_add, ← BitVec.add_assoc, four] using highRead
  have value : (logicalLanes 0 (physicalLanes state pointer))[lane] =
      low.toNat + 2 ^ 32 * high.toNat := by
    have view : (logicalLanes 0 (physicalLanes state pointer))[lane] =
        ramLane state (pointer + BitVec.ofNat 32 (Permutation.laneOffset lane)) := by
      simp only [logicalLanes, Fin.getElem_fin, Vector.getElem_ofFn,
        physicalLanes, Controller.physicalLane, Permutation.laneOffset]
    rw [view, ramLane]
    rw [ram_word_of_read lowRead, ram_word_of_read highRead]
  refine ⟨low, high, lowRead, highRead, value, ?_⟩
  rw [value]
  have := low.isLt
  have := high.isLt
  omega

theorem permutation_binding_at_boundary [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.WordMapping initial after pointer input output ∧
        Delegation.TraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input := by
  obtain ⟨pointer, after, pointerRead, trace, afterReadable, result⟩ :=
    call_permutation hp inverse accepted inputs tables aligned
  obtain ⟨otherPointer, otherRead, tracked⟩ := call_state_cells hp inverse accepted inputs tables aligned
  have same := (EStateM.Result.ok.inj (otherRead.symm.trans pointerRead)).1
  subst otherPointer
  have initialReadable : ∀ cell ∈ cells, ∃ value, cell.read initial = .ok value initial := by
    exact boundary_readable inputs.memory
  exact ⟨after, pointer, logicalLanes 0 (physicalLanes initial pointer),
    logicalLanes 0 (physicalLanes after pointer),
    ⟨pointerRead, lanes_at tracked initialReadable, lanes_at tracked afterReadable⟩, trace, result⟩

theorem permutation_binding [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.WordMapping initial after pointer input output ∧
        Delegation.TraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input :=
  permutation_binding_at_boundary hp inverse accepted inputs.toBoundaryInputs tables aligned

end Airbender.Keccak.Proofs
