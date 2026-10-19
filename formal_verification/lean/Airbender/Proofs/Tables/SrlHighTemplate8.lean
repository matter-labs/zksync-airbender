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

def template8 : Array Nat :=
  match (data.columns[1].blocks[8]? : Option Block) with
  | some (Block.periodic _ _ values) => values
  | _ => #[]

theorem template8_size : template8.size = 256 := by
  dsimp only [template8,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceLT,if_true]

theorem template8_values (i : Fin 256) :
    template8[i.val]? = some (((i.val + 1) % 256) * 256) := by
  have block_bound : i.val / 64 < 4 := by have := i.isLt; omega
  interval_cases block : i.val / 64
  · have chunk : ∀ j : Fin 64, template8[0 + j.val]? = some (((0 + j.val + 1) % 256) * 256) := by
      dsimp only [template8,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 0 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template8[64 + j.val]? = some (((64 + j.val + 1) % 256) * 256) := by
      dsimp only [template8,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 64 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template8[128 + j.val]? = some (((128 + j.val + 1) % 256) * 256) := by
      dsimp only [template8,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 128 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template8[192 + j.val]? = some (((192 + j.val + 1) % 256) * 256) := by
      dsimp only [template8,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 192 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩

end Airbender.Verification.SrlHighProofs
