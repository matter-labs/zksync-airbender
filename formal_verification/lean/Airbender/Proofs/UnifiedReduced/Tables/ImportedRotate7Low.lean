import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.Rotate7Data
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.UnifiedReduced.Setup.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem imported_rotate7low_output :
    checkBlocks (fun n => ((n / 256 ^^^ n % 256) % 128) * 2) 0
      nativeRotate7Data.columns[5].blocks.toList = true := by
  dsimp only [nativeRotate7Data, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp (config := { maxSteps := 1000000 }) only [raw_toList_append,
    checkBlocks_append_iff, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Block.length,
     Nat.reduceAdd, ]
  repeat' apply And.intro
  all_goals
    simp (config := { maxSteps := 1000000 }) only [checkBlocks_cons_iff,
      checkBlocks_nil, and_true, Block.length,
       Nat.reduceAdd, ]
    repeat' apply And.intro
    all_goals simp only [Block.get?, Block.length,
        ]
    all_goals decide +kernel

end Airbender.UnifiedReduced.Setup.Proofs
