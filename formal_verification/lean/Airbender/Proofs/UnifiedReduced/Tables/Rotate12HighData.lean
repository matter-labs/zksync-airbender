import Airbender.Data.Setup.UnifiedReduced.Native.Rotate12Data
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.LiteralSizes
import Mathlib.Tactic.IntervalCases

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def rotate12HighReferenceColumn : Column := ⟨Array.append #[
  .affine 16 0 0,
  .periodic 15 0 (Array.ofFn (fun i : Fin 256 => (i.val / 16 + 1) % 16)),
  .periodic 15 1 (Array.replicate 16 1)]
  (Array.ofFn (fun k : Fin 15 => Block.periodic 16 0
    (Array.ofFn (fun i : Fin 256 => (k.val + 1) ^^^ (i.val / 16)))))⟩

theorem rotate12_high_column : nativeRotate12Data.columns[5] = rotate12HighReferenceColumn := by
  dsimp only [nativeRotate12Data, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, rotate12HighReferenceColumn]
  apply congrArg Column.mk
  apply Array.ext
  · simp only [raw_literal_size, raw_size_append, Array.size_ofFn,
      List.length_cons, List.length_nil, Nat.reduceAdd]
  · intro index left right
    have small : index < 18 := by simpa only [raw_literal_size, List.length_cons, List.length_nil] using left
    interval_cases index
    all_goals simp only [
        List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
         ]
    all_goals rfl

end Airbender.UnifiedReduced.Setup.Proofs
