import Slop.KeccakSplit.Reference.Rounds.Chi00
import Slop.KeccakSplit.Reference.Rounds.Chi01
import Slop.KeccakSplit.Reference.Rounds.Chi02
import Slop.KeccakSplit.Reference.Rounds.Chi03
import Slop.KeccakSplit.Reference.Rounds.Chi04
import Slop.KeccakSplit.Reference.Rounds.Chi05
import Slop.KeccakSplit.Reference.Rounds.Chi06
import Slop.KeccakSplit.Reference.Rounds.Chi07
import Slop.KeccakSplit.Reference.Rounds.Chi08
import Slop.KeccakSplit.Reference.Rounds.Chi09
import Slop.KeccakSplit.Reference.Rounds.Chi10
import Slop.KeccakSplit.Reference.Rounds.Chi11
import Slop.KeccakSplit.Reference.Rounds.Chi12
import Slop.KeccakSplit.Reference.Rounds.Chi13
import Slop.KeccakSplit.Reference.Rounds.Chi14
import Slop.KeccakSplit.Reference.Rounds.Chi15
import Slop.KeccakSplit.Reference.Rounds.Chi16
import Slop.KeccakSplit.Reference.Rounds.Chi17
import Slop.KeccakSplit.Reference.Rounds.Chi18
import Slop.KeccakSplit.Reference.Rounds.Chi19
import Slop.KeccakSplit.Reference.Rounds.Chi20
import Slop.KeccakSplit.Reference.Rounds.Chi21
import Slop.KeccakSplit.Reference.Rounds.Chi22
import Slop.KeccakSplit.Reference.Rounds.Chi23

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- All twenty-four chi phases match the original Keccak reference. -/
theorem chi_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (chiPhase round state) =
      chi (logicalLanes (round.val + 1) state) := by
  fin_cases round
  · exact Rounds.chi_0 state
  · exact Rounds.chi_1 state
  · exact Rounds.chi_2 state
  · exact Rounds.chi_3 state
  · exact Rounds.chi_4 state
  · exact Rounds.chi_5 state
  · exact Rounds.chi_6 state
  · exact Rounds.chi_7 state
  · exact Rounds.chi_8 state
  · exact Rounds.chi_9 state
  · exact Rounds.chi_10 state
  · exact Rounds.chi_11 state
  · exact Rounds.chi_12 state
  · exact Rounds.chi_13 state
  · exact Rounds.chi_14 state
  · exact Rounds.chi_15 state
  · exact Rounds.chi_16 state
  · exact Rounds.chi_17 state
  · exact Rounds.chi_18 state
  · exact Rounds.chi_19 state
  · exact Rounds.chi_20 state
  · exact Rounds.chi_21 state
  · exact Rounds.chi_22 state
  · exact Rounds.chi_23 state

end Airbender.Keccak.Split.Call.Proofs
