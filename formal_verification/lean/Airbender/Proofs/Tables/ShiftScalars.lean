import Airbender.Review.Helpers.Tables.NativeShiftScalarRows
import Airbender.Proofs.Tables.ShiftScalarColumns
import Airbender.Proofs.Tables.SignFillLow
import Airbender.Proofs.Tables.SignFillHigh
import Airbender.Proofs.Tables.ShiftScalarBounds
import Airbender.Proofs.Mersenne31

namespace Airbender.Verification.ShiftScalarProofs
open Setup NativeShiftScalars
set_option warningAsError true
set_option Elab.async false

theorem sign_rows (i : Fin 2097152) : dataSignFill.rowNat i = (signFillRow i).push 52 := by
  ext lane bound
  interval_cases lane <;>
    simp [TableData.rowNat,signFillRow,sign_key,sign_tag,sign_low,sign_high]

theorem native_rows (kind : ShiftScalarKind) (i : Fin kind.length) :
    row kind i = (kind.row i).push kind.tag := by
  cases kind with
  | truncate => exact truncate_rows i
  | signFill => exact sign_rows i
  | range => exact range_rows i

theorem native_membership (kind : ShiftScalarKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    kind.table.Contains #[] query ↔ Contains kind query := by
  change (∃ i : Fin kind.length, query = (kind.row i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,by simp [native_rows,Vector.map_push]⟩
  · rintro ⟨i,same⟩
    refine ⟨i,?_⟩
    ext lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [native_rows,Vector.map_push,Vector.getElem_push,bound] using selected

private theorem canonical (n : Nat) (bound : n < 2097152) :
    (n : ZMod mersenne31Modulus).val = n := by
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by change n < 2147483647; omega)]

theorem truncate_result (query : Vector (ZMod mersenne31Modulus) 3)
    (member : Contains .truncate query) :
    query[0].val < 65536 ∧ query[1].val = query[0].val % 32 ∧ query[2] = 0 := by
  have clean : ∃ i : Fin 65536, query = (truncateShiftRow i).map Nat.cast :=
    (native_membership .truncate query).mpr member
  obtain ⟨i,rfl⟩ := clean
  have range := i.isLt
  have rem : i.val % 32 < 32 := Nat.mod_lt _ (by decide)
  simp [truncateShiftRow,canonical _ (by omega : i.val < 2097152),
    canonical _ (by omega : i.val % 32 < 2097152)]

theorem range_result (query : Vector (ZMod mersenne31Modulus) 3)
    (member : Contains .range query) :
    query[0].val < 65536 ∧ query[1] = 0 ∧ query[2] = 0 := by
  have clean : ∃ i : Fin 65536, query = (paddedRangeRow i).map Nat.cast :=
    (native_membership .range query).mpr member
  obtain ⟨i,rfl⟩ := clean
  have range := i.isLt
  simp [paddedRangeRow,canonical _ (by omega : i.val < 2097152)]

theorem sign_result (query : Vector (ZMod mersenne31Modulus) 3)
    (member : Contains .signFill query) :
    query[0].val < 2097152 ∧ query[1].val < 65536 ∧ query[2].val < 65536 ∧
      BitVec.ofNat 32 (query[1].val + 65536 * query[2].val) =
        if query[0].val % 65536 < 32768 then (0 : BitVec 32)
        else (BitVec.allOnes 32) <<< (32 - query[0].val / 65536) := by
  have clean : ∃ i : Fin 2097152, query = (signFillRow i).map Nat.cast :=
    (native_membership .signFill query).mpr member
  obtain ⟨i,rfl⟩ := clean
  have bounds := sign_mask i.val i.isLt
  simp only [signFillRow,Vector.getElem_map,Vector.getElem_mk,List.getElem_toArray,
    List.getElem_cons_zero,List.getElem_cons_succ,canonical _ i.isLt,
    canonical _ (by omega : signFillLow i.val < 2097152),
    canonical _ (by omega : signFillHigh i.val < 2097152)]
  exact ⟨i.isLt,bounds⟩

end Airbender.Verification.ShiftScalarProofs
