import Slop.KeccakSplit.Reference.Rounds.ParityA00
import Slop.KeccakSplit.Reference.Rounds.ParityB00
import Slop.KeccakSplit.Reference.Rounds.ParityA01
import Slop.KeccakSplit.Reference.Rounds.ParityB01
import Slop.KeccakSplit.Reference.Rounds.ParityA02
import Slop.KeccakSplit.Reference.Rounds.ParityB02
import Slop.KeccakSplit.Reference.Rounds.ParityA03
import Slop.KeccakSplit.Reference.Rounds.ParityB03
import Slop.KeccakSplit.Reference.Rounds.ParityA04
import Slop.KeccakSplit.Reference.Rounds.ParityB04
import Slop.KeccakSplit.Reference.Rounds.ParityA05
import Slop.KeccakSplit.Reference.Rounds.ParityB05
import Slop.KeccakSplit.Reference.Rounds.ParityA06
import Slop.KeccakSplit.Reference.Rounds.ParityB06
import Slop.KeccakSplit.Reference.Rounds.ParityA07
import Slop.KeccakSplit.Reference.Rounds.ParityB07
import Slop.KeccakSplit.Reference.Rounds.ParityA08
import Slop.KeccakSplit.Reference.Rounds.ParityB08
import Slop.KeccakSplit.Reference.Rounds.ParityA09
import Slop.KeccakSplit.Reference.Rounds.ParityB09
import Slop.KeccakSplit.Reference.Rounds.ParityA10
import Slop.KeccakSplit.Reference.Rounds.ParityB10
import Slop.KeccakSplit.Reference.Rounds.ParityA11
import Slop.KeccakSplit.Reference.Rounds.ParityB11
import Slop.KeccakSplit.Reference.Rounds.ParityA12
import Slop.KeccakSplit.Reference.Rounds.ParityB12
import Slop.KeccakSplit.Reference.Rounds.ParityA13
import Slop.KeccakSplit.Reference.Rounds.ParityB13
import Slop.KeccakSplit.Reference.Rounds.ParityA14
import Slop.KeccakSplit.Reference.Rounds.ParityB14
import Slop.KeccakSplit.Reference.Rounds.ParityA15
import Slop.KeccakSplit.Reference.Rounds.ParityB15
import Slop.KeccakSplit.Reference.Rounds.ParityA16
import Slop.KeccakSplit.Reference.Rounds.ParityB16
import Slop.KeccakSplit.Reference.Rounds.ParityA17
import Slop.KeccakSplit.Reference.Rounds.ParityB17
import Slop.KeccakSplit.Reference.Rounds.ParityA18
import Slop.KeccakSplit.Reference.Rounds.ParityB18
import Slop.KeccakSplit.Reference.Rounds.ParityA19
import Slop.KeccakSplit.Reference.Rounds.ParityB19
import Slop.KeccakSplit.Reference.Rounds.ParityA20
import Slop.KeccakSplit.Reference.Rounds.ParityB20
import Slop.KeccakSplit.Reference.Rounds.ParityA21
import Slop.KeccakSplit.Reference.Rounds.ParityB21
import Slop.KeccakSplit.Reference.Rounds.ParityA22
import Slop.KeccakSplit.Reference.Rounds.ParityB22
import Slop.KeccakSplit.Reference.Rounds.ParityA23
import Slop.KeccakSplit.Reference.Rounds.ParityB23

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- All 120 round parity calls match the original delayed-iota reference. -/
theorem parity_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  fin_cases round
  · refine ⟨Rounds.parity_lanes_0 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_0 state
    · exact Rounds.parity_columns_0 column zero state
  · refine ⟨Rounds.parity_lanes_1 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_1 state
    · exact Rounds.parity_columns_1 column zero state
  · refine ⟨Rounds.parity_lanes_2 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_2 state
    · exact Rounds.parity_columns_2 column zero state
  · refine ⟨Rounds.parity_lanes_3 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_3 state
    · exact Rounds.parity_columns_3 column zero state
  · refine ⟨Rounds.parity_lanes_4 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_4 state
    · exact Rounds.parity_columns_4 column zero state
  · refine ⟨Rounds.parity_lanes_5 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_5 state
    · exact Rounds.parity_columns_5 column zero state
  · refine ⟨Rounds.parity_lanes_6 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_6 state
    · exact Rounds.parity_columns_6 column zero state
  · refine ⟨Rounds.parity_lanes_7 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_7 state
    · exact Rounds.parity_columns_7 column zero state
  · refine ⟨Rounds.parity_lanes_8 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_8 state
    · exact Rounds.parity_columns_8 column zero state
  · refine ⟨Rounds.parity_lanes_9 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_9 state
    · exact Rounds.parity_columns_9 column zero state
  · refine ⟨Rounds.parity_lanes_10 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_10 state
    · exact Rounds.parity_columns_10 column zero state
  · refine ⟨Rounds.parity_lanes_11 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_11 state
    · exact Rounds.parity_columns_11 column zero state
  · refine ⟨Rounds.parity_lanes_12 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_12 state
    · exact Rounds.parity_columns_12 column zero state
  · refine ⟨Rounds.parity_lanes_13 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_13 state
    · exact Rounds.parity_columns_13 column zero state
  · refine ⟨Rounds.parity_lanes_14 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_14 state
    · exact Rounds.parity_columns_14 column zero state
  · refine ⟨Rounds.parity_lanes_15 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_15 state
    · exact Rounds.parity_columns_15 column zero state
  · refine ⟨Rounds.parity_lanes_16 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_16 state
    · exact Rounds.parity_columns_16 column zero state
  · refine ⟨Rounds.parity_lanes_17 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_17 state
    · exact Rounds.parity_columns_17 column zero state
  · refine ⟨Rounds.parity_lanes_18 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_18 state
    · exact Rounds.parity_columns_18 column zero state
  · refine ⟨Rounds.parity_lanes_19 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_19 state
    · exact Rounds.parity_columns_19 column zero state
  · refine ⟨Rounds.parity_lanes_20 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_20 state
    · exact Rounds.parity_columns_20 column zero state
  · refine ⟨Rounds.parity_lanes_21 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_21 state
    · exact Rounds.parity_columns_21 column zero state
  · refine ⟨Rounds.parity_lanes_22 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_22 state
    · exact Rounds.parity_columns_22 column zero state
  · refine ⟨Rounds.parity_lanes_23 state, fun column => ?_⟩
    by_cases zero : column = 0
    · subst zero
      exact Rounds.parity_column_zero_23 state
    · exact Rounds.parity_columns_23 column zero state

end Airbender.Keccak.Split.Call.Proofs
