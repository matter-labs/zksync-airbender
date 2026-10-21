import Airbender.Review.Circuits.Blake2Round.Tables.XorData
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Check the actual XOR output in every carry-aware seven-bit row. -/
theorem carry7_output_checks :
    checkBlocks (fun n => n / 128 % 128 ^^^ n % 128) 0
      xor7CarryData.columns[3].blocks.toList = true := by
  dsimp only [xor7CarryData, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 1000000 }) only [checkBlocks_cons_iff,
    checkBlocks_nil, and_true, Block.length, Array.size_ofFn,
    raw_size_append, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
    Array.size_ofFn, raw_size_append, raw_get_append]
  all_goals decide +kernel

end Airbender.Blake2Round.Proofs
