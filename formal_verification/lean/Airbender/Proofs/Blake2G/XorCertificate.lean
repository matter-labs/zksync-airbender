import Airbender.Proofs.Blake2G.XorCertificateBase
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

set_option maxHeartbeats 0 in
private theorem output9 : checkBlocks (fun n => n / 512 ^^^ n % 512) 0
    (xor9Data.columns[2]'(by omega)).blocks.toList = true := by
  dsimp only [xor9Data, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp (config := { maxSteps := 1000000 }) only [raw_toList_append,
    checkBlocks_append_iff, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Block.length, Array.size_ofFn,
    raw_size_append, Nat.reduceAdd, Nat.reduceMul]
  repeat' apply And.intro
  all_goals
    simp (config := { maxSteps := 1000000 }) only [checkBlocks_cons_iff,
      checkBlocks_nil, and_true, Block.length, Array.size_ofFn, raw_size_append,
      Nat.reduceAdd, Nat.reduceMul]
    repeat' apply And.intro
    all_goals simp only [Block.get?, Block.length, Array.getElem?_ofFn,
      Array.size_ofFn, raw_size_append, raw_get_append]
    all_goals decide +kernel

/-- Kernel certificates over all actual output blocks. Array/list identities
    and template getters are normalized before the bounded finite checks. -/
theorem imported_xor_output_checks (kind : Fin 5) :
    checkBlocks (fun n => n / 2 ^ (#v[8, 3, 4, 7, 9][kind]) ^^^
      n % 2 ^ (#v[8, 3, 4, 7, 9][kind])) 0
      (xorData kind).columns[2].blocks.toList = true := by
  fin_cases kind
  · exact XorCertificate.output8
  · exact XorCertificate.output3
  · exact XorCertificate.output4
  · exact XorCertificate.output7
  · exact output9

end Airbender.Blake2G.Proofs
