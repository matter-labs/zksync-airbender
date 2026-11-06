import Airbender.Review.Circuits.ReducedMachine.Tables.Shift
import Airbender.Proofs.ReducedMachine.NativePool

namespace Airbender.ReducedMachine.NativeSignFillProofs
open Setup NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Every one of the 128 actual native literal rows is checked in the kernel. -/
theorem rows : ∀ i : Fin 128, dataT20.rowNat i =
    #v[i.val,(signFillOutputs i.val)[0],(signFillOutputs i.val)[1],20] := by
  decide +kernel

theorem output_bounds : ∀ i : Fin 128,
    (signFillOutputs i.val)[0] < 65536 ∧ (signFillOutputs i.val)[1] < 65536 := by
  decide +kernel

private theorem canonical (n : Nat) (bound : n < 65536) :
    (n : ZMod mersenne31Modulus).val = n := by
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by change n < 2147483647; omega)]

theorem result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 20) :
    query[0].val < 128 ∧ query[1].val = (signFillOutputs query[0].val)[0] ∧
      query[2].val = (signFillOutputs query[0].val)[1] ∧
      query[1].val < 65536 ∧ query[2].val < 65536 := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region query member .signFill selected
  subst query
  have bound : i.val < 65536 := by have := i.isLt; change i.val < 128 at this; omega
  have low := (output_bounds i).1
  have high := (output_bounds i).2
  simp [NativePoolProofs.Region.data,TableData.row,rows,canonical _ bound,
    canonical _ low,canonical _ high,low,high]
  exact i.isLt

end Airbender.ReducedMachine.NativeSignFillProofs
