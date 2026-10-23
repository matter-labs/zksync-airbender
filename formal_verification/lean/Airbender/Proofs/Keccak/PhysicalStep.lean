import Airbender.Proofs.Keccak.PhysicalDefinitions
import Airbender.Proofs.Keccak.LaneFrame
import Airbender.Proofs.Keccak.MicroValue

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def physicalLanes (state : State) (pointer : BitVec 32) : LaneState :=
  fun lane => ramLane state (pointer + BitVec.ofNat 32 (8 * lane.val))

theorem micro_step_get (call : Fin 649) (state : LaneState) (physical : Fin 31) :
    microStep call state physical =
      let slot := (slotIndices call).toList.idxOf physical.val
      if h : slot < 6 then
        microValue (scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩)
          (fun lane : Fin 6 => state ⟨(slotIndices call)[lane.val]'lane.isLt, Controller.Proofs.rows_bound
    (Fin.ofNat 4096 ((scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩).packed + 2048)) lane⟩)
          ⟨slot, h⟩
      else state physical := by
  unfold microStep
  rfl

private theorem microValue_get_nat (control : ControlState) (bound : control.round.val < 25)
    (read : Fin 6 → Nat) (slot : Nat) (present : slot < 6) :
    (microWrites control (Vector.ofFn read))[slot] =
      microValue control read ⟨slot, present⟩ := by
  simpa only [Fin.getElem_fin] using micro_value_eq control bound read ⟨slot, present⟩

private theorem lane_observation_at (values : Vector Nat 6) (read : Fin 6 → Nat)
    (target : Nat → Nat) (observed : ∀ lane : Fin 6, read lane = target values[lane.val])
    (slot : Nat) (present : slot < 6) (physical : Nat)
    (index : values[slot] = physical) :
    read ⟨slot, present⟩ = target physical :=
  (observed ⟨slot, present⟩).trans (congrArg target index)

theorem native_physical_step [Fact p.Prime] {w : Nat → ZMod p}
    {pointer : BitVec 32} {before after : State} {cells : List Cell} {events : List MemoryAccess}
    (call : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩).packed)
    (mapped : statePointer w = Word.ofBitVec pointer)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .keccak w).memorySteps.map Trace.transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before)
    (observed : ∀ lane : Fin 6,
      Native.readLane w lane = ramLane before (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane.val]'lane.isLt)) ∧
      Native.writtenLane w lane = ramLane after (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane.val]'lane.isLt))) :
    physicalLanes after pointer = microStep call (physicalLanes before pointer) := by
  have reads : Vector.ofFn (Native.readLane w) = portReads call (physicalLanes before pointer) := by
    apply Vector.ext
    intro lane bound
    simpa only [Vector.getElem_ofFn, portReads, physicalLanes] using (observed ⟨lane, bound⟩).1
  have roundBound : (scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩).round.val < 25 := by
    simp only [scheduleControl]
    have := call.isLt
    omega
  have writes := row_micro_writes effects (scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩) roundBound control
  rw [reads] at writes
  funext physical
  let slot := (slotIndices call).toList.idxOf physical.val
  by_cases present : slot < 6
  · have index : (slotIndices call)[slot] = physical.val := by
      simpa only [Vector.getElem_toList] using
        List.getElem_idxOf (show (slotIndices call).toList.idxOf physical.val < (slotIndices call).toList.length by simpa using present)
    have value := congrArg (fun v : Vector Nat 6 => v[slot]) writes
    simp only [Native.writtenLanes, Vector.getElem_ofFn, portReads] at value
    have actual := lane_observation_at (slotIndices call) (Native.writtenLane w)
      (fun lane => ramLane after (pointer + BitVec.ofNat 32 (8 * lane)))
      (fun lane => (observed lane).2) slot present physical.val index
    rw [micro_step_get, dif_pos present]
    exact actual.symm.trans (value.trans (microValue_get_nat (scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩)
      roundBound (fun lane => physicalLanes before pointer
        ⟨(slotIndices call)[lane.val]'lane.isLt, Controller.Proofs.rows_bound
    (Fin.ofNat 4096 ((scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩).packed + 2048)) lane⟩) slot present))
  · have untouched : ∀ lane : Fin 6, (slotIndices call)[lane.val]'lane.isLt ≠ physical.val := by
      intro lane same
      have member : physical.val ∈ (slotIndices call).toList := by
        rw [← same]
        exact List.getElem_mem _
      have short := List.idxOf_lt_length_of_mem member
      exact present (by simpa only [Vector.length_toList] using short)
    have frame := @native_lane_frame p inferInstance w pointer before after cells events
      call effects active control mapped history permutation aligned tracked readable
      physical (fun lane => by
        change (slotIndices call)[lane.val]'lane.isLt ≠ physical.val
        exact untouched lane)
    rw [micro_step_get, dif_neg present]
    exact frame

end Airbender.Keccak.Proofs
