import Airbender.Review.Helpers.Tables.Shift.XorData
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Blake2G.Xor8Certificate

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

/-- Only the first byte differs in block layout. Check that boundary and reuse
    the kernel-checked certificate for the identical remaining imported blocks. -/
theorem xor_outputs :
    checkBlocks (fun n => n / 256 ^^^ n % 256) 0
      byteXorData.columns[2].blocks.toList = true := by
  have canonical : (Blake2G.xor8Data.columns[2]'(by decide)).blocks.toList =
      .affine 256 0 1 :: (Blake2G.xor8Data.columns[2]'(by decide)).blocks.toList.tail := by
    dsimp only [byteXorData, Blake2G.xor8Data, Vector.getElem_mk,
      Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [raw_toList_append, List.cons_append, List.nil_append]
    all_goals rfl
  have actual : byteXorData.columns[2].blocks.toList =
      .affine 1 0 0 :: .affine 255 1 1 :: byteXorData.columns[2].blocks.toList.drop 2 := by
    dsimp only [byteXorData, Blake2G.xor8Data, Vector.getElem_mk,
      Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [raw_toList_append, List.cons_append, List.nil_append]
    all_goals rfl
  have same : (Blake2G.xor8Data.columns[2]'(by decide)).blocks.toList.tail =
      byteXorData.columns[2].blocks.toList.drop 2 := by
    dsimp only [byteXorData, Blake2G.xor8Data, Vector.getElem_mk,
      Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [raw_toList_append, List.cons_append, List.nil_append]
    all_goals rfl
  have checked := Blake2G.Proofs.XorCertificate.output8
  rw [canonical, checkBlocks_cons_iff] at checked
  rw [actual, checkBlocks_cons_iff]
  refine ⟨by decide +kernel, ?_⟩
  rw [checkBlocks_cons_iff]
  refine ⟨by decide +kernel, ?_⟩
  change checkBlocks (fun n => n / 256 ^^^ n % 256) 256
    (byteXorData.columns[2].blocks.toList.drop 2) = true
  rw [← same]
  exact checked.2


end Airbender.Verification.ShiftCertificate
