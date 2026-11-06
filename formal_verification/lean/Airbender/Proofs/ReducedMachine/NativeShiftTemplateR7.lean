import Airbender.Review.Circuits.ReducedMachine.Tables.NativeData
import Airbender.Proofs.Tables.SrlHighTemplate7

namespace Airbender.ReducedMachine.NativeShiftTemplateR7Proofs
open Setup Setup.Proofs Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Only this already-emitted block is reduced, never a projection of the whole pool.
private def values : Array Nat := match dataT37Column2Block152 with
  | .periodic _ _ xs => xs
  | _ => #[]

private theorem size : values.size = 128 := by
  dsimp only [values,dataT37Column2Block152]
  simp only [raw_size_append,raw_literal_size,List.length_cons,List.length_nil,Nat.reduceAdd]

private theorem chunk0 : ∀ i : Fin 64,
    values[0 + i.val]? = some ((((0 + i.val) + 1) % 128) * 512) := by
  dsimp only [values,dataT37Column2Block152]
  simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem chunk1 : ∀ i : Fin 64,
    values[64 + i.val]? = some ((((64 + i.val) + 1) % 128) * 512) := by
  dsimp only [values,dataT37Column2Block152]
  simp only [raw_get_append,raw_literal_size,List.getElem?_toArray,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  decide +kernel

private theorem reads (i : Fin 128) : values[i.val]? = some ((((i.val) + 1) % 128) * 512) := by
  have bound : i.val / 64 < 2 := by have := i.isLt; omega
  interval_cases part : i.val / 64
  · have same : 0 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk0 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩
  · have same : 64 + i.val % 64 = i.val := by omega
    simpa only [same] using chunk1 ⟨i.val % 64,Nat.mod_lt _ (by decide)⟩

/-- Kernel-checked identity with the previously certified template; no table premise. -/
theorem block : dataT37Column2Block152 =
    Block.periodic 512 0 SrlHighProofs.template7 := by
  have same : values = SrlHighProofs.template7 := by
    apply Array.ext
    · exact size.trans SrlHighProofs.template7_size.symm
    · intro i hi hj
      have inside : i < 128 := by simpa only [size] using hi
      have value := (reads ⟨i,inside⟩).trans (SrlHighProofs.template7_values ⟨i,inside⟩).symm
      simpa only [Array.getElem?_eq_getElem hi,Array.getElem?_eq_getElem hj,
        Option.some.injEq] using value
  calc
    dataT37Column2Block152 = Block.periodic 512 0 values := rfl
    _ = _ := congrArg (Block.periodic 512 0) same

end Airbender.ReducedMachine.NativeShiftTemplateR7Proofs
