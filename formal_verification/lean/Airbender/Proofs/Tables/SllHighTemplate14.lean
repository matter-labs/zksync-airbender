import Airbender.Review.Helpers.Tables.NativeSllHighRows
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.LiteralSizes
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.SllHighProofs
open Setup Setup.Proofs NativeSllHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def template14 : Array Nat :=
  match (data.columns[2].blocks[71]? : Option Block) with
  | some (Block.periodic _ _ values) => values
  | _ => #[]

theorem template14_size : template14.size = 4 := by
  dsimp only [template14,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]

theorem template14_values (i : Fin 4) : template14[i.val]? = some (i.val * 16384) := by
  have complete : ∀ j : Fin 4, template14[j.val]? = some (j.val * 16384) := by
    dsimp only [template14,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
    simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
    decide +kernel
  exact complete i

end Airbender.Verification.SllHighProofs
