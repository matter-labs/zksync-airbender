import Airbender.Proofs.Keccak.SplitCallReference
import Airbender.Proofs.Keccak.PermutationSchedule

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

abbrev LaneState := Fin 31 → Nat

/-- Apply exactly the lane writes of one public split-call reference. -/
def microStep (index : Fin 361) (state : LaneState) : LaneState :=
  let input := Vector.ofFn fun lane : Fin 7 => state (slots index)[lane]
  fun physical =>
    let slot := (slots index).toList.idxOf physical
    if active : slot < slotCount (kindAt index.val) then
      (result index input)[slot]'(lt_of_lt_of_le active (slot_count_bound _))
    else state physical

def parityPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 5 (fun state column => microStep ⟨15 * round.val + column.val, by omega⟩ state) state

def thetaRhoPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 5 (fun state column => microStep ⟨15 * round.val + 5 + column.val, by omega⟩ state) state

def chiPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 5 (fun state row => microStep ⟨15 * round.val + 10 + row.val, by omega⟩ state) state

/-- Read logical lanes in the unchanged Clean Keccak coordinate convention. -/
def logicalLanes (round : Nat) (state : LaneState) : Vector Nat 25 :=
  Vector.ofFn fun lane => state ⟨Controller.physicalLane round lane,
    Nat.lt_trans (Controller.Proofs.physical_bound round lane) (by decide)⟩

end Airbender.Keccak.Split.Call.Proofs
