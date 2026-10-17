import Airbender.Review.Helpers.Tables.Shift.OrData
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem or_outputs :
    checkBlocks (fun n => n / 256 ||| n % 256) 0
      byteOrData.columns[2].blocks.toList = true := by
  dsimp only [byteOrData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp (config := { maxSteps := 1000000 }) only [raw_toList_append,
    checkBlocks_append_iff, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Block.length, Array.size_ofFn,
    raw_size_append, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals
    simp (config := { maxSteps := 1000000 }) only [checkBlocks_cons_iff,
      checkBlocks_nil, and_true, Block.length, Array.size_ofFn,
      raw_size_append, Nat.reduceAdd, Nat.reduceMul]
    repeat' apply And.intro
    all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
      Array.size_ofFn, raw_size_append, raw_get_append]
    all_goals decide +kernel

end Airbender.Verification.ShiftCertificate
