import Airbender.Proofs.Blake2Round.Carry8Extents

namespace Airbender.Blake2Round.Proofs.Carry8Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem output_part2 :
    checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart2
      carry8ColumnBlocks2.toList = true := by
  dsimp only [carry8ColumnBlocks2, carry8ColumnStart2]
  simp (config := { maxSteps := 1000000 }) only [raw_toList_append,
    List.cons_append, List.nil_append, checkBlocks_cons_iff,
    checkBlocks_nil, and_true, Block.length,
      ]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length,
      ]
  all_goals decide +kernel


end Airbender.Blake2Round.Proofs.Carry8Certificate
