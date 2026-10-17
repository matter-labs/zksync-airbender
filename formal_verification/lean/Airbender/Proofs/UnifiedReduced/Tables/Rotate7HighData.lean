import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.Rotate7Data

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def rotate7HighReferenceColumn : Column := ⟨#[
  .affine 128 0 0,
  .periodic 127 0 (Array.ofFn (fun i : Fin 256 => 1 - i.val / 128)),
  .affine 256 1 0,
  .periodic 127 0 (Array.ofFn (fun i : Fin 256 => i.val / 128)),
  .affine 128 0 0]⟩

theorem rotate7_high_column : nativeRotate7Data.columns[2] = rotate7HighReferenceColumn := by
  dsimp only [nativeRotate7Data, rotate7HighReferenceColumn, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals rfl

end Airbender.UnifiedReduced.Setup.Proofs
