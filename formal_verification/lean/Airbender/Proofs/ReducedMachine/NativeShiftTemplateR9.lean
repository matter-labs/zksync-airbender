import Airbender.Review.Circuits.ReducedMachine.Tables.NativeData
import Airbender.Proofs.Tables.SrlHighTemplate9

namespace Airbender.ReducedMachine.NativeShiftTemplateR9Proofs
open Setup Setup.Proofs Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Only this already-emitted block is reduced, never a projection of the whole pool.
private def values : Array Nat := match dataT37Column2Block154 with
  | .periodic _ _ xs => xs
  | _ => #[]

private theorem size : values.size = 512 := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_size_append,raw_literal_size,List.length_cons,List.length_nil,Nat.reduceAdd]

private theorem chunk0 : ∀ i : Fin 64,
    values[0 + i.val]? = some ((((0 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk1 : ∀ i : Fin 64,
    values[64 + i.val]? = some ((((64 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk2 : ∀ i : Fin 64,
    values[128 + i.val]? = some ((((128 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk3 : ∀ i : Fin 64,
    values[192 + i.val]? = some ((((192 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk4 : ∀ i : Fin 64,
    values[256 + i.val]? = some ((((256 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk5 : ∀ i : Fin 64,
    values[320 + i.val]? = some ((((320 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk6 : ∀ i : Fin 64,
    values[384 + i.val]? = some ((((384 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk7 : ∀ i : Fin 64,
    values[448 + i.val]? = some ((((448 + i.val) + 1) % 512) * 128) := by
  dsimp only [values,dataT37Column2Block154]
  simp only [raw_get_append,raw_size_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem reads (i : Fin 512) : values[i.val]? = some ((((i.val) + 1) % 512) * 128) := by
  have bound : i.val / 64 < 8 := by have := i.isLt; omega
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

/-- Kernel-checked identity with the previously certified template; no table premise. -/
theorem block : dataT37Column2Block154 =
    Block.periodic 128 0 SrlHighProofs.template9 := by
  have same : values = SrlHighProofs.template9 := by
    apply Array.ext
    · exact size.trans SrlHighProofs.template9_size.symm
    · intro i hi hj
      have inside : i < 512 := by simpa only [size] using hi
      have value := (reads ⟨i,inside⟩).trans (SrlHighProofs.template9_values ⟨i,inside⟩).symm
      simpa only [Array.getElem?_eq_getElem hi,Array.getElem?_eq_getElem hj,
        Option.some.injEq] using value
  calc
    dataT37Column2Block154 = Block.periodic 128 0 values := rfl
    _ = _ := congrArg (Block.periodic 128 0) same

end Airbender.ReducedMachine.NativeShiftTemplateR9Proofs
