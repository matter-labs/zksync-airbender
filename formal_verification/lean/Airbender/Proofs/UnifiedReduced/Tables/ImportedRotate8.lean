import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.Rotate8Data
import Airbender.Proofs.Blake2G.Xor8Certificate

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

/-- Bind the imported output column to the already checked byte-XOR certificate.
    Normalize projections first so equality checking does not expand the checker. -/
theorem imported_rotate8_output : checkBlocks (fun n => n / 256 ^^^ n % 256) 0
    nativeRotate8Data.columns[5].blocks.toList = true := by
  have same : nativeRotate8Data.columns[5].blocks =
      (Airbender.Blake2G.xor8Data.columns[2]'(by decide)).blocks := by
    dsimp only [nativeRotate8Data, Airbender.Blake2G.xor8Data, Vector.getElem_mk,
      Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [same]
  exact Airbender.Blake2G.Proofs.XorCertificate.output8


end Airbender.UnifiedReduced.Setup.Proofs
