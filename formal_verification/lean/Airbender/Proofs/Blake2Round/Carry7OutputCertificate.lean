import Airbender.Review.Circuits.Blake2Round.Tables.XorData
import Airbender.Proofs.Blake2G.Xor7Certificate
import Airbender.Proofs.Tables.CyclicXorCertificate

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000
@[irreducible] private noncomputable def shortBlocks : List Block :=
  (Blake2G.xor7Data.columns[2]'(by decide)).blocks.toList

private theorem shape : xor7CarryData.columns[3].blocks.toList =
    shortBlocks ++ (shortBlocks ++ shortBlocks) := by
  unfold shortBlocks
  dsimp only [xor7CarryData, Blake2G.xor7Data, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]


/-- Exact coverage of the native seven-bit carry output column. -/
theorem carry7_output_extent :
    (xor7CarryData.columns[3].blocks.toList.map Block.length).sum = 49152 := by
  dsimp only [xor7CarryData, Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp (config := { maxSteps := 1000000 }) [Block.length]

/-- Reuse the seven-bit XOR certificate on each of the three native carry cycles. -/
theorem carry7_output_checks :
    checkBlocks (fun n => n / 128 % 128 ^^^ n % 128) 0
      xor7CarryData.columns[3].blocks.toList = true := by
  apply cyclic_xor7_check shortBlocks _ shape carry7_output_extent
  unfold shortBlocks
  exact Blake2G.Proofs.XorCertificate.output7

end Airbender.Blake2Round.Proofs
