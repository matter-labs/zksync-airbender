import Slop.Keccak.LaneFrame
import Slop.Keccak.MicroValue

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

abbrev LaneState := Fin 31 → Nat

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

end Airbender.Keccak.Proofs
