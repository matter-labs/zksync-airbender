import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow00
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh00
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow01
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh01
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow02
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh02
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow03
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh03
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow04
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh04
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow05
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh05
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow06
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh06
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow07
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh07
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow08
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh08
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow09
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh09
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow10
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh10
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow11
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh11
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow12
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh12
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow13
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh13
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow14
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh14
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow15
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh15
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow16
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh16
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow17
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh17
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow18
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh18
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow19
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh19
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow20
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh20
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow21
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh21
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow22
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh22
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoLow23
import Slop.KeccakSplit.Reference.Rounds.ThetaRhoHigh23

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
