import Airbender.Review.Circuits.Blake2Round.Tables.Setup
import Airbender.Proofs.Blake2G.ImportedXor

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- The round artifact's own four columns equal the corresponding G columns.
    This is structural equality of independently imported native data. -/
theorem xor_region_projection (kind : Fin 5) (n : Nat) :
    xorRegionRow kind n =
      let row := Blake2G.xorRegionRow kind n
      #v[row[0], row[1], row[2], row[8]] := by
  fin_cases kind <;> apply Vector.ext
  all_goals intro j hj
  all_goals interval_cases j
  all_goals simp only [xorRegionRow, Blake2G.xorRegionRow, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals rfl

/-- Recover the shared mathematical XOR characterization from this circuit's
    actual setup artifact, without assuming a cross-artifact equivalence. -/
theorem setup_row_characterization (index : Fin 344384) :
    setupRow index =
      let row := Blake2G.referenceSetupRow (fun _ => Vector.replicate 7 0)
        ⟨index.val, by have bound := index.isLt; omega⟩
      #v[row[0], row[1], row[2], row[8]] := by
  have bound := index.isLt
  unfold setupRow Blake2G.referenceSetupRow
  dsimp only [xor8DataRegion, xor3DataRegion, xor4DataRegion, xor7DataRegion, xor9DataRegion]
  split_ifs
  all_goals first
    | { rw [xor_region_projection, Blake2G.Proofs.xor_region_reference _ _ (by
          change _ < 65536; omega)]; rfl }
    | { rw [xor_region_projection, Blake2G.Proofs.xor_region_reference _ _ (by
          change _ < 64; omega)]; rfl }
    | { rw [xor_region_projection, Blake2G.Proofs.xor_region_reference _ _ (by
          change _ < 256; omega)]; rfl }
    | { rw [xor_region_projection, Blake2G.Proofs.xor_region_reference _ _ (by
          change _ < 16384; omega)]; rfl }
    | { rw [xor_region_projection, Blake2G.Proofs.xor_region_reference _ _ (by
          change _ < 262144; omega)]; rfl }

theorem xor_region_native_cast (kind : Fin 5) (index : Fin (xorData kind).length) :
    (xorRegionRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((xorData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus)) := by
  have offset : (xorData kind).offset = 0 := by fin_cases kind <;> rfl
  apply Vector.ext
  intro j hj
  simp [xorRegionRow, TableData.row, offset, signedValue_cast]

end Airbender.Blake2Round.Proofs
