import Slop.Keccak.LaneFrame
import Slop.Keccak.MicroValue

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

abbrev LaneState := Fin 31 → Nat

def physicalLanes (state : State) (pointer : BitVec 32) : LaneState :=
  fun lane => ramLane state (pointer + BitVec.ofNat 32 (8 * lane.val))

def slotIndices (call : Fin 649) : Vector Nat 6 :=
  Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨call.val, by omega⟩).packed + 2048))

def portReads (call : Fin 649) (state : LaneState) : Vector Nat 6 :=
  Vector.ofFn fun lane => state ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩

def microStep (call : Fin 649) (state : LaneState) : LaneState :=
  let read := fun lane : Fin 6 => state ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩
  fun physical =>
    let slot := (slotIndices call).toList.idxOf physical.val
    if h : slot < 6 then microValue (scheduleControl ⟨call.val, by omega⟩) read ⟨slot, h⟩ else state physical

theorem micro_step_get (call : Fin 649) (state : LaneState) (physical : Fin 31) :
    microStep call state physical =
      if h : (slotIndices call).toList.idxOf physical.val < 6 then
        microValue (scheduleControl ⟨call.val, by omega⟩)
          (fun lane => state ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩)
          ⟨(slotIndices call).toList.idxOf physical.val, h⟩
      else state physical := rfl

theorem native_physical_step [Fact p.Prime] {w : Nat → ZMod p}
    {pointer : BitVec 32} {before after : State} {cells : List Cell} {events : List MemoryAccess}
    (call : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨call.val, by omega⟩).packed)
    (mapped : statePointer w = Word.ofBitVec pointer)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .keccak w).memorySteps.map Trace.transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before)
    (observed : ∀ lane : Fin 6,
      Native.readLane w lane = ramLane before (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane])) ∧
      Native.writtenLane w lane = ramLane after (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane]))) :
    physicalLanes after pointer = microStep call (physicalLanes before pointer) := by
  have reads : Vector.ofFn (Native.readLane w) = portReads call (physicalLanes before pointer) := by
    apply Vector.ext
    intro lane bound
    simpa only [Vector.getElem_ofFn, portReads, physicalLanes] using (observed ⟨lane, bound⟩).1
  have roundBound : (scheduleControl ⟨call.val, by omega⟩).round.val < 25 := by
    simp only [scheduleControl]
    have := call.isLt
    omega
  have writes := row_micro_writes effects (scheduleControl ⟨call.val, by omega⟩) roundBound control
  rw [reads] at writes
  funext physical
  let slot := (slotIndices call).toList.idxOf physical.val
  by_cases present : slot < 6
  · have index : (slotIndices call)[slot] = physical.val := by
      simpa only [Vector.getElem_toList] using
        List.getElem_idxOf (show (slotIndices call).toList.idxOf physical.val < (slotIndices call).toList.length by simpa using present)
    have value := congrArg (fun v : Vector Nat 6 => v[slot]) writes
    simp only [Native.writtenLanes, Vector.getElem_ofFn] at value
    have actual := (observed ⟨slot, present⟩).2
    simp only [Fin.getElem_fin] at actual
    rw [index] at actual
    rw [micro_step_get, dite_eq_left present]
    exact actual.symm.trans (value.trans (micro_value_eq (scheduleControl ⟨call.val, by omega⟩)
      roundBound (fun lane => physicalLanes before pointer
        ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩) ⟨slot, present⟩))
  · have untouched : ∀ lane : Fin 6, (slotIndices call)[lane] ≠ physical.val := by
      intro lane same
      have member : physical.val ∈ (slotIndices call).toList := by
        rw [← same]
        exact List.getElem_mem _
      have short := List.idxOf_lt_length_of_mem member
      exact present (by simpa only [Vector.length_toList] using short)
    have frame := @native_lane_frame p inferInstance w pointer before after cells events
      call effects active control mapped history permutation aligned tracked readable
      physical (fun lane => by
        change (slotIndices call)[lane] ≠ physical.val
        exact untouched lane)
    rw [micro_step_get, dite_eq_right present]
    exact frame

end Airbender.Keccak.Proofs
