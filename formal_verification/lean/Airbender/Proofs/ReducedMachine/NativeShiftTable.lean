import Airbender.Proofs.ReducedMachine.NativeShiftRows
import Airbender.Proofs.ReducedMachine.NativePool

namespace Airbender.ReducedMachine.NativeShiftTableProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem canonical (n : Nat) (bound : n < 4194304) :
    (n : ZMod mersenne31Modulus).val = n := by
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by change n < 2147483647; omega)]

/-- Actual complete-pool membership, not a supplied region or table equivalence. -/
theorem result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 37) :
    query[0].val < 4194304 ∧ query[1].val = (shiftOutputs query[0].val)[0] ∧
      query[2].val = (shiftOutputs query[0].val)[1] ∧
      query[1].val < 65536 ∧ query[2].val < 65536 := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region query member .shift selected
  subst query
  have bound : i.val < 4194304 := i.isLt
  have low := (NativeShiftArithmeticProofs.output_bounds i.val).1
  have high := (NativeShiftArithmeticProofs.output_bounds i.val).2
  have actual : (NativePoolProofs.Region.data .shift).row i =
      (#v[i.val,(shiftOutputs i.val)[0],(shiftOutputs i.val)[1],37] : Vector Nat 4).map
        (fun (n : Nat) => (n : ZMod mersenne31Modulus)) :=
    congrArg (fun v : Vector Nat 4 => v.map (fun (n : Nat) => (n : ZMod mersenne31Modulus)))
      (NativeShiftRowProofs.rows i)
  rw [actual]
  simp [canonical _ bound,
    canonical _ (by omega : (shiftOutputs i.val)[0] < 4194304),
    canonical _ (by omega : (shiftOutputs i.val)[1] < 4194304),low,high]
  exact bound

end Airbender.ReducedMachine.NativeShiftTableProofs
