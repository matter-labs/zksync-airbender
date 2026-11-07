import Airbender.Proofs.Keccak.MicroValueDefinitions
import Airbender.Proofs.Keccak.ControllerLayout
import Airbender.Review.Trace.Workers.Keccak.Call

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

abbrev LaneState := Fin 31 → Nat

def slotIndices (call : Fin 649) : Vector Nat 6 :=
  Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩).packed + 2048))

def portReads (call : Fin 649) (state : LaneState) : Vector Nat 6 :=
  Vector.ofFn fun lane : Fin 6 => state ⟨(slotIndices call)[lane.val]'lane.isLt, Controller.Proofs.rows_bound
    (Fin.ofNat 4096 ((scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩).packed + 2048)) lane⟩

def microStep (call : Fin 649) (state : LaneState) : LaneState :=
  let read := fun lane : Fin 6 => state ⟨(slotIndices call)[lane.val]'lane.isLt, Controller.Proofs.rows_bound
    (Fin.ofNat 4096 ((scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩).packed + 2048)) lane⟩
  fun physical =>
    let slot := (slotIndices call).toList.idxOf physical.val
    if h : slot < 6 then microValue (scheduleControl ⟨call.val, Nat.lt_trans call.isLt (by decide : 649 < 650)⟩) read ⟨slot, h⟩ else state physical

end Airbender.Keccak.Proofs
