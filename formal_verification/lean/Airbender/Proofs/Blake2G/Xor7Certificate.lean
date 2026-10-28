import Airbender.Data.Setup.Blake2G.XorData
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs.XorCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- The seven-bit certificate has its own cache boundary, so edits to the
    smaller XOR certificates do not rerun its exhaustive kernel check. -/
theorem output7 : checkBlocks (fun n => n / 128 ^^^ n % 128) 0
    (xor7Data.columns[2]'(by omega)).blocks.toList = true := by
  dsimp only [xor7Data, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  simp only [checkBlocks_cons_iff, checkBlocks_nil, and_true, Block.length,
    Array.size_ofFn, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
    Array.size_ofFn]
  all_goals decide +kernel


end Airbender.Blake2G.Proofs.XorCertificate
