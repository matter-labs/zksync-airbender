import Airbender.Review.Circuits.ReducedMachine.Tables.NativeData
import Airbender.Proofs.Tables.SllHighTemplate12

namespace Airbender.ReducedMachine.NativeShiftTemplateL12Proofs
open Setup Setup.Proofs Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Only this already-emitted block is reduced, never a projection of the whole pool.
private def values : Array Nat := match dataT37Column1Block69 with
  | .periodic _ _ xs => xs
  | _ => #[]

private theorem size : values.size = 16 := by
  rfl

private theorem chunk0 : ∀ i : Fin 16,
    values[0 + i.val]? = some ((0 + i.val) * 4096) := by
  decide +kernel

private theorem reads (i : Fin 16) : values[i.val]? = some ((i.val) * 4096) := by
  simpa only [Nat.zero_add] using chunk0 i

/-- Kernel-checked identity with the previously certified template; no table premise. -/
theorem block : dataT37Column1Block69 =
    Block.periodic 4096 0 SllHighProofs.template12 := by
  have same : values = SllHighProofs.template12 := by
    apply Array.ext
    · exact size.trans SllHighProofs.template12_size.symm
    · intro i hi hj
      have inside : i < 16 := by simpa only [size] using hi
      have value := (reads ⟨i,inside⟩).trans (SllHighProofs.template12_values ⟨i,inside⟩).symm
      simpa only [Array.getElem?_eq_getElem hi,Array.getElem?_eq_getElem hj,
        Option.some.injEq] using value
  calc
    dataT37Column1Block69 = Block.periodic 4096 0 values := rfl
    _ = _ := congrArg (Block.periodic 4096 0) same

end Airbender.ReducedMachine.NativeShiftTemplateL12Proofs
