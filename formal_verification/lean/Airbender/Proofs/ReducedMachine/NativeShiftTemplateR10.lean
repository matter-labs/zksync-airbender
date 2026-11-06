import Airbender.Review.Circuits.ReducedMachine.Tables.NativeData
import Airbender.Proofs.Tables.SrlHighTemplate10

namespace Airbender.ReducedMachine.NativeShiftTemplateR10Proofs
open Setup Setup.Proofs Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Only this already-emitted block is reduced, never a projection of the whole pool.
private def values : Array Nat := match dataT37Column2Block155 with
  | .periodic _ _ xs => xs
  | _ => #[]

private theorem size : values.size = 1024 := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_size_append,raw_literal_size,List.length_cons,List.length_nil,Nat.reduceAdd]

private theorem chunk0 : ∀ i : Fin 64,
    values[0 + i.val]? = some ((((0 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk1 : ∀ i : Fin 64,
    values[64 + i.val]? = some ((((64 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk2 : ∀ i : Fin 64,
    values[128 + i.val]? = some ((((128 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk3 : ∀ i : Fin 64,
    values[192 + i.val]? = some ((((192 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk4 : ∀ i : Fin 64,
    values[256 + i.val]? = some ((((256 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk5 : ∀ i : Fin 64,
    values[320 + i.val]? = some ((((320 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk6 : ∀ i : Fin 64,
    values[384 + i.val]? = some ((((384 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk7 : ∀ i : Fin 64,
    values[448 + i.val]? = some ((((448 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk8 : ∀ i : Fin 64,
    values[512 + i.val]? = some ((((512 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk9 : ∀ i : Fin 64,
    values[576 + i.val]? = some ((((576 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk10 : ∀ i : Fin 64,
    values[640 + i.val]? = some ((((640 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk11 : ∀ i : Fin 64,
    values[704 + i.val]? = some ((((704 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk12 : ∀ i : Fin 64,
    values[768 + i.val]? = some ((((768 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk13 : ∀ i : Fin 64,
    values[832 + i.val]? = some ((((832 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk14 : ∀ i : Fin 64,
    values[896 + i.val]? = some ((((896 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk15 : ∀ i : Fin 64,
    values[960 + i.val]? = some ((((960 + i.val) + 1) % 1024) * 64) := by
  dsimp only [values,dataT37Column2Block155]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem reads (i : Fin 1024) : values[i.val]? = some ((((i.val) + 1) % 1024) * 64) := by
  have bound : i.val / 64 < 16 := by have := i.isLt; omega
  interval_cases part : i.val / 64
  · have same : 0 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk0 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 64 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk1 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 128 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk2 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 192 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk3 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 256 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk4 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 320 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk5 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 384 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk6 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 448 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk7 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 512 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk8 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 576 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk9 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 640 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk10 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 704 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk11 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 768 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk12 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 832 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk13 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 896 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk14 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 960 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk15 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩

/-- Kernel-checked identity with the previously certified template; no table premise. -/
theorem block : dataT37Column2Block155 =
    Block.periodic 64 0 SrlHighProofs.template10 := by
  have same : values = SrlHighProofs.template10 := by
    apply Array.ext
    · exact size.trans SrlHighProofs.template10_size.symm
    · intro i hi hj
      have inside : i < 1024 := by simpa only [size] using hi
      have value := (reads ⟨i,inside⟩).trans (SrlHighProofs.template10_values ⟨i,inside⟩).symm
      simpa only [Array.getElem?_eq_getElem hi,Array.getElem?_eq_getElem hj,
        Option.some.injEq] using value
  calc
    dataT37Column2Block155 = Block.periodic 64 0 values := rfl
    _ = _ := congrArg (Block.periodic 64 0) same

end Airbender.ReducedMachine.NativeShiftTemplateR10Proofs
