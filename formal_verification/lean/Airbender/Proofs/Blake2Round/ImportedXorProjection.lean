import Airbender.Review.Circuits.Blake2Round.Tables.Setup
import Airbender.Review.Circuits.Blake2G.Tables.XorData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- The first input, XOR result and native tag are structurally identical
    across the independently imported setups. The second input has a different
    lossless block partition and is characterized separately. -/
theorem plain_xor_region_projection (kind : Fin 3) (n : Nat) :
    (let row := xorRegionRow ⟨kind.val, by omega⟩ n;
      #v[row[0], row[2], row[5]]) =
      let row := Blake2G.xorRegionRow (#v[(0 : Fin 5), 3, 4][kind]) n
      #v[row[0], row[2], row[8]] := by
  fin_cases kind <;> apply Vector.ext
  all_goals intro j hj
  all_goals interval_cases j
  all_goals simp only [xorRegionRow, Blake2G.xorRegionRow, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals rfl

end Airbender.Blake2Round.Proofs
