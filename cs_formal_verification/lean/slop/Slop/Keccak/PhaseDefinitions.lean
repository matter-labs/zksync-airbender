import Slop.Keccak.PermutationSchedule
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

def iotaPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 5 (fun state i => microStep ⟨27 * round.val + i.val, by omega⟩ state) state

def mixPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 2 (fun state i => microStep ⟨27 * round.val + 5 + i.val, by omega⟩ state) state

def thetaPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 5 (fun state i => microStep ⟨27 * round.val + 7 + i.val, by omega⟩ state) state

def rhoPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 5 (fun state i => microStep ⟨27 * round.val + 12 + i.val, by omega⟩ state) state

def chiPhase (round : Fin 24) (state : LaneState) : LaneState :=
  Fin.foldl 10 (fun state i => microStep ⟨27 * round.val + 17 + i.val, by omega⟩ state) state

end Airbender.Keccak.Proofs
