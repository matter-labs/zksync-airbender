import Airbender.Proofs.Blake2Round.NativeXorRowReads
import Airbender.Proofs.Blake2Round.ImportedXorProjection
import Airbender.Proofs.Blake2Round.NativePlainXorKeys
import Airbender.Proofs.Blake2Round.NativeXorPadding
import Airbender.Proofs.Blake2G.ImportedXor

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem row_from_projection (row : Vector Nat 6) (a b c tag : Nat)
    (projected : #v[row[0], row[2], row[5]] = #v[a, c, tag])
    (second : row[1] = b) (zero3 : row[3] = 0) (zero4 : row[4] = 0) :
    row = #v[a, b, c, 0, 0, tag] := by
  have first := congrArg (fun v : Vector Nat 3 => v[0]) projected
  have output := congrArg (fun v : Vector Nat 3 => v[1]) projected
  have selected := congrArg (fun v : Vector Nat 3 => v[2]) projected
  simp only [Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ] at first output selected
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp only [Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals assumption

/-- Reuse the checked G XOR outputs through independently imported data. -/
theorem plain_region_reference (kind : Fin 3) (n : Nat)
    (hn : n < (xorData ⟨kind.val, by omega⟩).length) :
    xorRegionRow ⟨kind.val, by omega⟩ n =
      let a := n / (#v[256, 128, 512][kind]);
      let b := n % (#v[256, 128, 512][kind]);
      #v[a, b, a ^^^ b, 0, 0, #v[4, 19, 20][kind]] := by
  have bound : n < (Blake2G.xorData (#v[(0 : Fin 5), 3, 4][kind])).length := by
    fin_cases kind <;> exact hn
  have projected :
      #v[(xorRegionRow ⟨kind.val, by omega⟩ n)[0],
        (xorRegionRow ⟨kind.val, by omega⟩ n)[2],
        (xorRegionRow ⟨kind.val, by omega⟩ n)[5]] =
      #v[n / (#v[256, 128, 512][kind]),
        n / (#v[256, 128, 512][kind]) ^^^ n % (#v[256, 128, 512][kind]),
        #v[4, 19, 20][kind]] := by
    refine (plain_xor_region_projection kind n).trans ?_
    rw [Blake2G.Proofs.xor_region_reference _ _ bound]
    fin_cases kind <;> rfl
  apply row_from_projection _ _ _ _ _ projected
  · rw [xorRegionRow_read, plain_second_get kind n hn, Option.getD_some]
  · rw [xorRegionRow_read, plain_padding_get kind ⟨0, by decide⟩ n hn, Option.getD_some]
  · rw [xorRegionRow_read, plain_padding_get kind ⟨1, by decide⟩ n hn, Option.getD_some]

end Airbender.Blake2Round.Proofs
