import Airbender.Review.Circuits.ReducedMachine.Tables.NativeData
import Airbender.Proofs.Tables.SrlHighTemplate5

namespace Airbender.ReducedMachine.NativeShiftTemplateR5Proofs
open Setup Setup.Proofs Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Only this already-emitted block is reduced, never a projection of the whole pool.
private def values : Array Nat := match dataT37Column2Block150 with
  | .periodic _ _ xs => xs
  | _ => #[]

private theorem size : values.size = 32 := by
  rfl

private theorem chunk0 : ∀ i : Fin 32,
    values[0 + i.val]? = some ((((0 + i.val) + 1) % 32) * 2048) := by
  decide +kernel

private theorem reads (i : Fin 32) : values[i.val]? = some ((((i.val) + 1) % 32) * 2048) := by
  simpa only [Nat.zero_add] using chunk0 i

/-- Kernel-checked identity with the previously certified template; no table premise. -/
theorem block : dataT37Column2Block150 =
    Block.periodic 2048 0 SrlHighProofs.template5 := by
  have same : values = SrlHighProofs.template5 := by
    apply Array.ext
    · exact size.trans SrlHighProofs.template5_size.symm
    · intro i hi hj
      have inside : i < 32 := by simpa only [size] using hi
      have value := (reads ⟨i,inside⟩).trans (SrlHighProofs.template5_values ⟨i,inside⟩).symm
      simpa only [Array.getElem?_eq_getElem hi,Array.getElem?_eq_getElem hj,
        Option.some.injEq] using value
  calc
    dataT37Column2Block150 = Block.periodic 2048 0 values := rfl
    _ = _ := congrArg (Block.periodic 2048 0) same

end Airbender.ReducedMachine.NativeShiftTemplateR5Proofs
