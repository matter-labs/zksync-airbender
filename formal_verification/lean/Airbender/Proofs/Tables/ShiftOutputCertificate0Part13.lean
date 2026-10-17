import Airbender.Proofs.Tables.ShiftOutputPartitions0
import Airbender.Proofs.Tables.ShiftOutputNormalization

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output0_part13 :
    checkBlocks (outputByte 0) 222706 output0Blocks13.toList = true := by
  rw [outputByte_normalized]
  dsimp only [output0Blocks13]
  simp (config := { maxSteps := 10000000 }) only [raw_toList_append, checkBlocks_append_iff, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Block.length, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals
    simp only [checkBlocks_cons_iff, checkBlocks_nil, and_true, Block.length]
    repeat' apply And.intro
    all_goals simp only [Block.get?, Block.length]
    all_goals decide +kernel

end Airbender.Verification.ShiftCertificate
