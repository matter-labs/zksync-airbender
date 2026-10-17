import Airbender.Proofs.Blake2G.Xor9Partitions

namespace Airbender.Blake2G.Proofs.Xor9Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output_part7 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart7
      xor9ColumnBlocks7.toList = true := by
  dsimp only [xor9ColumnBlocks7, xor9ColumnStart7]
  simp (config := { maxSteps := 1000000 }) only [checkBlocks_cons_iff,
      checkBlocks_nil, and_true, Block.length,
       ]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length,
        ]
  all_goals decide +kernel

end Airbender.Blake2G.Proofs.Xor9Certificate
