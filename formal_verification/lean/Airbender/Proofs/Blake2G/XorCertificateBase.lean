import Airbender.Proofs.Blake2G.Xor7Certificate
import Airbender.Proofs.Blake2G.Xor8Certificate
import Airbender.Data.Setup.Blake2G.XorData
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs.XorCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem output3 : checkBlocks (fun n => n / 8 ^^^ n % 8) 0
    (xor3Data.columns[2]'(by omega)).blocks.toList = true := by
  dsimp only [xor3Data, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [checkBlocks_cons_iff, checkBlocks_nil, and_true, Block.length,
    Array.size_ofFn, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
    Array.size_ofFn]
  all_goals decide +kernel

theorem output4 : checkBlocks (fun n => n / 16 ^^^ n % 16) 0
    (xor4Data.columns[2]'(by omega)).blocks.toList = true := by
  dsimp only [xor4Data, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [checkBlocks_cons_iff, checkBlocks_nil, and_true, Block.length,
    Array.size_ofFn, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
    Array.size_ofFn]
  all_goals decide +kernel



end Airbender.Blake2G.Proofs.XorCertificate
