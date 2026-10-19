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

def template9 : Array Nat :=
  match (data.columns[2].blocks[66]? : Option Block) with
  | some (Block.periodic _ _ values) => values
  | _ => #[]

theorem template9_size : template9.size = 128 := by
  dsimp only [template9,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]

theorem template9_values (i : Fin 128) : template9[i.val]? = some (i.val * 512) := by
  have block_bound : i.val / 64 < 2 := by have := i.isLt; omega
  interval_cases block : i.val / 64
  · have chunk : ∀ j : Fin 64, template9[0 + j.val]? = some ((0 + j.val) * 512) := by
      dsimp only [template9,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 0 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template9[64 + j.val]? = some ((64 + j.val) * 512) := by
      dsimp only [template9,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 64 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩

end Airbender.Verification.SllHighProofs
