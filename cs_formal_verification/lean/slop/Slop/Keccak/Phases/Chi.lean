import Slop.Keccak.Phases.Chi.Part0
import Slop.Keccak.Phases.Chi.Part1
import Slop.Keccak.Phases.Chi.Part2
import Slop.Keccak.Phases.Chi.Part3

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem chi_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (chiPhase round state) = chi (logicalLanes (round.val + 1) state) := by
  fin_cases round
  · exact chi_lanes_0 state
  · exact chi_lanes_1 state
  · exact chi_lanes_2 state
  · exact chi_lanes_3 state
  · exact chi_lanes_4 state
  · exact chi_lanes_5 state
  · exact chi_lanes_6 state
  · exact chi_lanes_7 state
  · exact chi_lanes_8 state
  · exact chi_lanes_9 state
  · exact chi_lanes_10 state
  · exact chi_lanes_11 state
  · exact chi_lanes_12 state
  · exact chi_lanes_13 state
  · exact chi_lanes_14 state
  · exact chi_lanes_15 state
  · exact chi_lanes_16 state
  · exact chi_lanes_17 state
  · exact chi_lanes_18 state
  · exact chi_lanes_19 state
  · exact chi_lanes_20 state
  · exact chi_lanes_21 state
  · exact chi_lanes_22 state
  · exact chi_lanes_23 state

end Airbender.Keccak.Proofs
