import Airbender.Review.Helpers.Tables.NativeSrlHighRows
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.LiteralSizes
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.SrlHighProofs
open Setup Setup.Proofs NativeSrlHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def template6 : Array Nat :=
  match (data.columns[1].blocks[6]? : Option Block) with
  | some (Block.periodic _ _ values) => values
  | _ => #[]

theorem template6_size : template6.size = 64 := by
  dsimp only [template6,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceLT,if_true]

theorem template6_values (i : Fin 64) :
    template6[i.val]? = some (((i.val + 1) % 64) * 1024) := by
  have complete : ∀ j : Fin 64, template6[j.val]? = some (((j.val + 1) % 64) * 1024) := by
    dsimp only [template6,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
    simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceLT,if_true]
    decide +kernel
  exact complete i

end Airbender.Verification.SrlHighProofs
