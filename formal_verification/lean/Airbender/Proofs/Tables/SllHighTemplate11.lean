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

def template11 : Array Nat :=
  match (data.columns[2].blocks[68]? : Option Block) with
  | some (Block.periodic _ _ values) => values
  | _ => #[]

theorem template11_size : template11.size = 32 := by
  dsimp only [template11,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]

theorem template11_values (i : Fin 32) : template11[i.val]? = some (i.val * 2048) := by
  have complete : ∀ j : Fin 32, template11[j.val]? = some (j.val * 2048) := by
    dsimp only [template11,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
    simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
    decide +kernel
  exact complete i

end Airbender.Verification.SllHighProofs
