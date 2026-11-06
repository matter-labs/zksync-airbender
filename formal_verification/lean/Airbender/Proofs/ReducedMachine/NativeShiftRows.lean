import Airbender.Proofs.ReducedMachine.NativeShiftLow
import Airbender.Proofs.ReducedMachine.NativeShiftHigh

namespace Airbender.ReducedMachine.NativeShiftRowProofs
open Setup NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?,Block.length,if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts,if_pos (Int.natCast_nonneg _),Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks,if_pos bound]

private theorem key (i : Fin 4194304) : dataT37.columns[0].get? i.val = some i.val := by
  change (⟨#[.affine 4194304 0 1]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 4194304 0 1 i.val i.isLt

private theorem tag (i : Fin 4194304) : dataT37.columns[3].get? i.val = some 37 := by
  change (⟨#[.affine 4194304 37 0]⟩ : Column).get? i.val = _
  rw [single_get _ _ i.isLt]
  simpa using affine_get 4194304 37 0 i.val i.isLt

-- Prove tuple projection once with abstract values, not expanded shift arithmetic.
private theorem row_of_getters (data : TableData 4) (i : Fin data.length)
    (a b c d : Nat)
    (h0 : data.columns[0].get? i.val = some a)
    (h1 : data.columns[1].get? i.val = some b)
    (h2 : data.columns[2].get? i.val = some c)
    (h3 : data.columns[3].get? i.val = some d) : data.rowNat i = #v[a,b,c,d] := by
  ext lane bound
  simp only [TableData.rowNat,Vector.getElem_map]
  interval_cases lane
  · change (data.columns[0].get? i.val).getD 0 = a
    rw [h0]
    rfl
  · change (data.columns[1].get? i.val).getD 0 = b
    rw [h1]
    rfl
  · change (data.columns[2].get? i.val).getD 0 = c
    rw [h2]
    rfl
  · change (data.columns[3].get? i.val).getD 0 = d
    rw [h3]
    rfl

/-- Every actual native row has its exact key, bounded arithmetic outputs and tag. -/
theorem rows (i : Fin 4194304) : dataT37.rowNat i =
    #v[i.val,(shiftOutputs i.val)[0],(shiftOutputs i.val)[1],37] :=
  row_of_getters dataT37 i i.val (shiftOutputs i.val)[0] (shiftOutputs i.val)[1] 37
    (key i) (NativeShiftLowProofs.output i) (NativeShiftHighProofs.output i) (tag i)

end Airbender.ReducedMachine.NativeShiftRowProofs
