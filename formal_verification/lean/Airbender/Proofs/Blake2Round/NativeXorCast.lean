import Airbender.Review.Circuits.Blake2Round.Tables.XorData

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem xor_region_native_cast (kind : Fin 6) (index : Fin (xorData kind).length) :
    (xorRegionRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((xorData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus)) := by
  have offset : (xorData kind).offset = 0 := by fin_cases kind <;> rfl
  apply Vector.ext
  intro j hj
  simp [xorRegionRow, TableData.row, offset, signedValue_cast]

end Airbender.Blake2Round.Proofs
