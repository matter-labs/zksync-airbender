import Airbender.Proofs.Blake2G.Xor9Partitions

namespace Airbender.Blake2G.Proofs.Xor9Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output_part56 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart56
      xor9ColumnBlocks56.toList = true := by
  dsimp only [xor9ColumnBlocks56, xor9ColumnStart56]
  simp (config := { maxSteps := 1000000 }) only [checkBlocks_cons_iff,
      checkBlocks_nil, and_true, Block.length, Array.size_ofFn,
      Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
      Array.size_ofFn,  ]
  all_goals decide +kernel

end Airbender.Blake2G.Proofs.Xor9Certificate
