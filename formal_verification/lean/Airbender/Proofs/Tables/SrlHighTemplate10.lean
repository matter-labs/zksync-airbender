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

def template10 : Array Nat :=
  match (data.columns[1].blocks[10]? : Option Block) with
  | some (Block.periodic _ _ values) => values
  | _ => #[]

theorem template10_size : template10.size = 1024 := by
  dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceLT,if_true]

theorem template10_values (i : Fin 1024) :
    template10[i.val]? = some (((i.val + 1) % 1024) * 64) := by
  have block_bound : i.val / 64 < 16 := by have := i.isLt; omega
  interval_cases block : i.val / 64
  · have chunk : ∀ j : Fin 64, template10[0 + j.val]? = some (((0 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 0 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[64 + j.val]? = some (((64 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 64 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[128 + j.val]? = some (((128 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 128 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[192 + j.val]? = some (((192 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 192 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[256 + j.val]? = some (((256 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 256 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[320 + j.val]? = some (((320 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 320 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[384 + j.val]? = some (((384 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 384 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[448 + j.val]? = some (((448 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 448 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[512 + j.val]? = some (((512 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 512 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[576 + j.val]? = some (((576 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 576 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[640 + j.val]? = some (((640 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 640 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[704 + j.val]? = some (((704 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 704 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[768 + j.val]? = some (((768 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 768 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[832 + j.val]? = some (((832 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 832 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[896 + j.val]? = some (((896 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 896 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have chunk : ∀ j : Fin 64, template10[960 + j.val]? = some (((960 + j.val + 1) % 1024) * 64) := by
      dsimp only [template10,data,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
      simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_true]
      decide +kernel
    have same : 960 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩

end Airbender.Verification.SrlHighProofs
