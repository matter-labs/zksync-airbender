import Airbender.Proofs.ReducedMachine.NativePool
import Airbender.Proofs.Tables.ShiftScalarColumns

namespace Airbender.ReducedMachine.NativeTruncationProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The actual reduced columns are definitionally identical to the certified
    truncation columns. Native offsets differ and are not equated. -/
theorem shared_columns : dataT47.columns = NativeShiftScalars.dataTruncate.columns := rfl

theorem rows (i : Fin 65536) : dataT47.rowNat i = #v[i.val,i.val % 32,0,47] := by
  have same : dataT47.rowNat i = NativeShiftScalars.dataTruncate.rowNat i := rfl
  rw [same,ShiftScalarProofs.truncate_rows]
  rfl

private theorem canonical (n : Nat) (bound : n < 65536) :
    (n : ZMod mersenne31Modulus).val = n := by
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by change n < 2147483647; omega)]

/-- Full native pool membership enforces all truncation fields, including zero
    in the otherwise unused third field. No region-equivalence premise is used. -/
theorem result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 47) :
    query[0].val < 65536 ∧ query[1].val = query[0].val % 32 ∧ query[2] = 0 := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region query member .truncate selected
  subst query
  have bound : i.val < 65536 := i.isLt
  have low : i.val % 32 < 65536 := by have := Nat.mod_lt i.val (by decide : 0 < 32); omega
  simp [NativePoolProofs.Region.data,TableData.row,rows,canonical _ bound,canonical _ low]
  exact bound

end Airbender.ReducedMachine.NativeTruncationProofs
