import Airbender.Data.Setup.Blake2Round.XorData
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Check every actual combined four-bit and three-bit XOR output. -/
theorem combined_output_checks :
    checkBlocks (fun n => (n / 1024 ^^^ n / 8 % 16) + 16 * (n / 128 % 8 ^^^ n % 8)) 0
      xor4x3Data.columns[4].blocks.toList = true := by
  dsimp only [xor4x3Data, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 1000000 }) only [checkBlocks_cons_iff,
    checkBlocks_nil, and_true, Block.length,
    raw_size_append, Nat.reduceAdd, ]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length,
     raw_size_append, raw_get_append]
  all_goals decide +kernel

end Airbender.Blake2Round.Proofs
