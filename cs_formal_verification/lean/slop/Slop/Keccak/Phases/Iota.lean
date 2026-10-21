import Slop.Keccak.Phases.Iota.Part0
import Slop.Keccak.Phases.Iota.Part1
import Slop.Keccak.Phases.Iota.Part2
import Slop.Keccak.Phases.Iota.Part3

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 2000000

theorem iota_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (iotaPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) := by
  fin_cases round
  · exact iota_lanes_0 state
  · exact iota_lanes_1 state
  · exact iota_lanes_2 state
  · exact iota_lanes_3 state
  · exact iota_lanes_4 state
  · exact iota_lanes_5 state
  · exact iota_lanes_6 state
  · exact iota_lanes_7 state
  · exact iota_lanes_8 state
  · exact iota_lanes_9 state
  · exact iota_lanes_10 state
  · exact iota_lanes_11 state
  · exact iota_lanes_12 state
  · exact iota_lanes_13 state
  · exact iota_lanes_14 state
  · exact iota_lanes_15 state
  · exact iota_lanes_16 state
  · exact iota_lanes_17 state
  · exact iota_lanes_18 state
  · exact iota_lanes_19 state
  · exact iota_lanes_20 state
  · exact iota_lanes_21 state
  · exact iota_lanes_22 state
  · exact iota_lanes_23 state

theorem iota_phase_parities (round : Fin 24) (state : LaneState) (column : Fin 5) :
    iotaPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column] := by
  fin_cases round
  · exact iota_parities_0 state column
  · exact iota_parities_1 state column
  · exact iota_parities_2 state column
  · exact iota_parities_3 state column
  · exact iota_parities_4 state column
  · exact iota_parities_5 state column
  · exact iota_parities_6 state column
  · exact iota_parities_7 state column
  · exact iota_parities_8 state column
  · exact iota_parities_9 state column
  · exact iota_parities_10 state column
  · exact iota_parities_11 state column
  · exact iota_parities_12 state column
  · exact iota_parities_13 state column
  · exact iota_parities_14 state column
  · exact iota_parities_15 state column
  · exact iota_parities_16 state column
  · exact iota_parities_17 state column
  · exact iota_parities_18 state column
  · exact iota_parities_19 state column
  · exact iota_parities_20 state column
  · exact iota_parities_21 state column
  · exact iota_parities_22 state column
  · exact iota_parities_23 state column

end Airbender.Keccak.Proofs
