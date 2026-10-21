import Airbender.Proofs.Blake2Round.Carry8Partitions

namespace Airbender.Blake2Round.Proofs.Carry8Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem extent24 :
    (carry8ColumnBlocks24.toList.map Block.length).sum = carry8ColumnSize24 := by
  dsimp only [carry8ColumnBlocks24, carry8ColumnSize24]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output_part24 :
    checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart24
      carry8ColumnBlocks24.toList = true := by
  dsimp only [carry8ColumnBlocks24, carry8ColumnStart24]
  simp (config := { maxSteps := 1000000 }) only [raw_toList_append,
    List.cons_append, List.nil_append, checkBlocks_cons_iff,
    checkBlocks_nil, and_true, Block.length, Array.size_ofFn,
    raw_size_append, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
    Array.size_ofFn, raw_size_append, raw_get_append]
  all_goals decide +kernel

end Airbender.Blake2Round.Proofs.Carry8Certificate
