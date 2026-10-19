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

def template7 : Array Nat :=
  match (data.columns[2].blocks[64]? : Option Block) with
  | some (Block.periodic _ _ values) => values
  | _ => #[]

theorem template7_size : template7.size = 512 := by
  dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]

theorem template7_values (i : Fin 512) : template7[i.val]? = some (i.val * 128) := by
  have block_bound : i.val / 64 < 8 := by have := i.isLt; omega
  interval_cases block : i.val / 64
  · have chunk : ∀ j : Fin 64, template7[0 + j.val]? = some ((0 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 0 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template7[64 + j.val]? = some ((64 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 64 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template7[128 + j.val]? = some ((128 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 128 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template7[192 + j.val]? = some ((192 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 192 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template7[256 + j.val]? = some ((256 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 256 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template7[320 + j.val]? = some ((320 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 320 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template7[384 + j.val]? = some ((384 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 384 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template7[448 + j.val]? = some ((448 + j.val) * 128) := by
      dsimp only [template7,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
      decide +kernel
    have same : 448 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩

end Airbender.Verification.SllHighProofs
