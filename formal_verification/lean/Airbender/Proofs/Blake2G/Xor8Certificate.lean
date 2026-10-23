import Airbender.Review.Circuits.Blake2G.Tables.XorData
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs.XorCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- The byte-XOR certificate is independent of the smaller Blake2G tables.
    Other families import this checked proof without rebuilding those checks. -/
theorem output8 : checkBlocks (fun n => n / 256 ^^^ n % 256) 0
    (xor8Data.columns[2]'(by omega)).blocks.toList = true := by
  dsimp only [xor8Data, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  simp only [checkBlocks_cons_iff, checkBlocks_nil, and_true, Block.length,
    Array.size_ofFn, raw_size_append, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
    Array.size_ofFn, raw_size_append, raw_get_append]
  all_goals decide +kernel

end Airbender.Blake2G.Proofs.XorCertificate
