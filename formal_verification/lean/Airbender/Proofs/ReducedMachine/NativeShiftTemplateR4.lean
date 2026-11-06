import Airbender.Review.Circuits.ReducedMachine.Tables.NativeData
import Airbender.Proofs.Tables.SrlHighTemplate4

namespace Airbender.ReducedMachine.NativeShiftTemplateR4Proofs
open Setup Setup.Proofs Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Only this already-emitted block is reduced, never a projection of the whole pool.
private def values : Array Nat := match dataT37Column2Block149 with
  | .periodic _ _ xs => xs
  | _ => #[]

private theorem size : values.size = 16 := by
  rfl

private theorem chunk0 : ∀ i : Fin 16,
    values[0 + i.val]? = some ((((0 + i.val) + 1) % 16) * 4096) := by
  decide +kernel

private theorem reads (i : Fin 16) : values[i.val]? = some ((((i.val) + 1) % 16) * 4096) := by
  simpa only [Nat.zero_add] using chunk0 i

/-- Kernel-checked identity with the previously certified template; no table premise. -/
theorem block : dataT37Column2Block149 =
    Block.periodic 4096 0 SrlHighProofs.template4 := by
  have same : values = SrlHighProofs.template4 := by
    apply Array.ext
    · exact size.trans SrlHighProofs.template4_size.symm
    · intro i hi hj
      have inside : i < 16 := by simpa only [size] using hi
      have value := (reads ⟨i,inside⟩).trans (SrlHighProofs.template4_values ⟨i,inside⟩).symm
      simpa only [Array.getElem?_eq_getElem hi,Array.getElem?_eq_getElem hj,
        Option.some.injEq] using value
  calc
    dataT37Column2Block149 = Block.periodic 4096 0 values := rfl
    _ = _ := congrArg (Block.periodic 4096 0) same

end Airbender.ReducedMachine.NativeShiftTemplateR4Proofs
