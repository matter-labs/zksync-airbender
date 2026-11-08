module
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow00
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh00
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow01
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh01
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow02
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh02
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow03
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh03
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow04
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh04
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow05
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh05
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow06
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh06
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow07
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh07
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow08
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh08
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow09
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh09
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow10
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh10
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow11
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh11
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow12
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh12
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow13
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh13
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow14
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh14
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow15
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh15
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow16
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh16
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow17
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh17
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow18
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh18
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow19
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh19
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow20
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh20
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow21
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh21
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow22
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh22
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow23
public import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh23

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- All twenty-four theta+rho phases match the original Keccak reference. -/
theorem theta_rho_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (thetaRhoPhase round state) =
      rhoPi (thetaXor (logicalLanes round.val state)
        (thetaD (Vector.ofFn fun column : Fin 5 => state ⟨25 + column.val, by omega⟩))) := by
  fin_cases round
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_0 state lane low
      else Rounds.thetaRho_high_0 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_1 state lane low
      else Rounds.thetaRho_high_1 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_2 state lane low
      else Rounds.thetaRho_high_2 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_3 state lane low
      else Rounds.thetaRho_high_3 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_4 state lane low
      else Rounds.thetaRho_high_4 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_5 state lane low
      else Rounds.thetaRho_high_5 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_6 state lane low
      else Rounds.thetaRho_high_6 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_7 state lane low
      else Rounds.thetaRho_high_7 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_8 state lane low
      else Rounds.thetaRho_high_8 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_9 state lane low
      else Rounds.thetaRho_high_9 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_10 state lane low
      else Rounds.thetaRho_high_10 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_11 state lane low
      else Rounds.thetaRho_high_11 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_12 state lane low
      else Rounds.thetaRho_high_12 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_13 state lane low
      else Rounds.thetaRho_high_13 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_14 state lane low
      else Rounds.thetaRho_high_14 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_15 state lane low
      else Rounds.thetaRho_high_15 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_16 state lane low
      else Rounds.thetaRho_high_16 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_17 state lane low
      else Rounds.thetaRho_high_17 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_18 state lane low
      else Rounds.thetaRho_high_18 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_19 state lane low
      else Rounds.thetaRho_high_19 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_20 state lane low
      else Rounds.thetaRho_high_20 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_21 state lane low
      else Rounds.thetaRho_high_21 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_22 state lane low
      else Rounds.thetaRho_high_22 state lane (by omega) bound
  · exact Vector.ext fun lane bound => if low : lane < 13 then Rounds.thetaRho_low_23 state lane low
      else Rounds.thetaRho_high_23 state lane (by omega) bound

end Airbender.Keccak.Split.Call.Proofs
