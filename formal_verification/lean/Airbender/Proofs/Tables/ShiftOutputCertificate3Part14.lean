import Airbender.Proofs.Tables.ShiftOutputPartitions3
import Airbender.Proofs.Tables.ShiftOutputNormalization

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output3_part14 :
    checkBlocks (outputByte 3) 216065 output3Blocks14.toList = true := by
  rw [outputByte_normalized]
  dsimp only [output3Blocks14]
  simp (config := { maxSteps := 10000000 }) only [raw_toList_append, checkBlocks_append_iff, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Block.length, Array.size_ofFn, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals
    simp only [checkBlocks_cons_iff, checkBlocks_nil, and_true, Block.length]
    repeat' apply And.intro
    all_goals simp only [Block.get?, Block.length]
    all_goals decide +kernel

end Airbender.Verification.ShiftCertificate
