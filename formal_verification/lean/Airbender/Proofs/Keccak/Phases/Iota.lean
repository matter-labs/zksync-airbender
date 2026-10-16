import Airbender.Proofs.Keccak.Phases.IotaPart0
import Airbender.Proofs.Keccak.Phases.IotaPart1
import Airbender.Proofs.Keccak.Phases.IotaPart2
import Airbender.Proofs.Keccak.Phases.IotaPart3
import Airbender.Proofs.Keccak.Phases.IotaPart4
import Airbender.Proofs.Keccak.Phases.IotaPart5

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false

theorem iota_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (iotaPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) := by
  fin_cases round
  · exact IotaPart0.lanes 0 state
  · exact IotaPart0.lanes 1 state
  · exact IotaPart0.lanes 2 state
  · exact IotaPart0.lanes 3 state
  · exact IotaPart1.lanes 0 state
  · exact IotaPart1.lanes 1 state
  · exact IotaPart1.lanes 2 state
  · exact IotaPart1.lanes 3 state
  · exact IotaPart2.lanes 0 state
  · exact IotaPart2.lanes 1 state
  · exact IotaPart2.lanes 2 state
  · exact IotaPart2.lanes 3 state
  · exact IotaPart3.lanes 0 state
  · exact IotaPart3.lanes 1 state
  · exact IotaPart3.lanes 2 state
  · exact IotaPart3.lanes 3 state
  · exact IotaPart4.lanes 0 state
  · exact IotaPart4.lanes 1 state
  · exact IotaPart4.lanes 2 state
  · exact IotaPart4.lanes 3 state
  · exact IotaPart5.lanes 0 state
  · exact IotaPart5.lanes 1 state
  · exact IotaPart5.lanes 2 state
  · exact IotaPart5.lanes 3 state

theorem iota_phase_parities (round : Fin 24) (state : LaneState) (column : Fin 5) :
    iotaPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column] := by
  fin_cases round
  · exact IotaPart0.parities 0 state column
  · exact IotaPart0.parities 1 state column
  · exact IotaPart0.parities 2 state column
  · exact IotaPart0.parities 3 state column
  · exact IotaPart1.parities 0 state column
  · exact IotaPart1.parities 1 state column
  · exact IotaPart1.parities 2 state column
  · exact IotaPart1.parities 3 state column
  · exact IotaPart2.parities 0 state column
  · exact IotaPart2.parities 1 state column
  · exact IotaPart2.parities 2 state column
  · exact IotaPart2.parities 3 state column
  · exact IotaPart3.parities 0 state column
  · exact IotaPart3.parities 1 state column
  · exact IotaPart3.parities 2 state column
  · exact IotaPart3.parities 3 state column
  · exact IotaPart4.parities 0 state column
  · exact IotaPart4.parities 1 state column
  · exact IotaPart4.parities 2 state column
  · exact IotaPart4.parities 3 state column
  · exact IotaPart5.parities 0 state column
  · exact IotaPart5.parities 1 state column
  · exact IotaPart5.parities 2 state column
  · exact IotaPart5.parities 3 state column

end Airbender.Keccak.Proofs
