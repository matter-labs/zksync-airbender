import Airbender.Proofs.Tables.RowViews
import Airbender.Proofs.UnifiedReduced.Tables.ImportedBinaryRows
import Airbender.Proofs.UnifiedReduced.Tables.ImportedControlRows
import Airbender.Proofs.UnifiedReduced.Tables.ImportedConditional
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotateRows
import Airbender.Proofs.UnifiedReduced.Tables.ReferenceRows

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

@[simp] theorem logical_offset_0 : logicalFixedOffset 0 = 0 := rfl
@[simp] theorem logical_offset_1 : logicalFixedOffset 1 = 1 := rfl
@[simp] theorem logical_offset_2 : logicalFixedOffset 2 = 257 := rfl
@[simp] theorem logical_offset_3 : logicalFixedOffset 3 = 65793 := rfl
@[simp] theorem logical_offset_4 : logicalFixedOffset 4 = 131329 := rfl
@[simp] theorem logical_offset_5 : logicalFixedOffset 5 = 196865 := rfl
@[simp] theorem logical_offset_6 : logicalFixedOffset 6 = 262401 := rfl
@[simp] theorem logical_offset_7 : logicalFixedOffset 7 = 524545 := rfl
@[simp] theorem logical_offset_8 : logicalFixedOffset 8 = 655617 := rfl
@[simp] theorem logical_offset_9 : logicalFixedOffset 9 = 721153 := rfl
@[simp] theorem logical_offset_10 : logicalFixedOffset 10 = 786689 := rfl
@[simp] theorem logical_offset_11 : logicalFixedOffset 11 = 786817 := rfl
@[simp] theorem logical_offset_12 : logicalFixedOffset 12 = 852353 := rfl
@[simp] theorem logical_offset_13 : logicalFixedOffset 13 = 917889 := rfl
@[simp] theorem logical_offset_14 : logicalFixedOffset 14 = 983425 := rfl
@[simp] theorem logical_offset_15 : logicalFixedOffset 15 = 1048961 := rfl

private theorem ordinary_tag (kind : Fin 7) (n : Nat) (bound : n < (shiftData kind).length) :
    (shiftRegionRow kind n)[9] = (shiftRegion kind).id := by
  by_cases zero : kind.val = 0
  · have same : kind = 0 := Fin.ext zero
    subst kind
    have nzero : n = 0 := by change n < 1 at bound; omega
    subst n
    simp only [shiftRegionRow, Vector.getElem_map]
    change (byteZeroData.columns[9].get? 0).getD 0 = 0
    decide +kernel
  · have shape : (shiftData kind).columns[9] =
        Column.mk #[.affine (shiftData kind).length (shiftRegion kind).id 0] := by
      fin_cases kind
      · exact False.elim (zero rfl)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    simp [shiftRegionRow, shape, Column.get?, getFromBlocks, Block.get?, Block.length, bound]

private theorem binary_region (kind : Fin 7) (n : Nat) (bound : n < (shiftData kind).length) :
    nativeFixedRow ⟨kind.val, Nat.lt_trans kind.isLt (by decide : 7 < 15)⟩ n =
      (shiftRegionRow kind n).set 9 (binaryTag (shiftRegionRow kind n)[9]) := by
  let lengths : Vector Nat 7 := #v[1, 256, 65536, 65536, 65536, 65536, 262144]
  have nativeLength : (nativeFixedData ⟨kind.val, Nat.lt_trans kind.isLt (by decide : 7 < 15)⟩).length = lengths[kind] := by
    fin_cases kind <;> rfl
  have ordinaryLength : (shiftData kind).length = lengths[kind] := by
    fin_cases kind <;> rfl
  have extent : (nativeFixedData ⟨kind.val, Nat.lt_trans kind.isLt (by decide : 7 < 15)⟩).length = (shiftData kind).length :=
    nativeLength.trans ordinaryLength.symm
  rw [imported_binary_region kind n (by rw [extent]; exact bound), ordinary_tag kind n bound]
  fin_cases kind <;> rfl

/-- The original binary proof interface follows from the actual unified regions. -/
theorem binaryRow_eq_reference (index : Fin 524545) :
    binaryRow index = referenceBinaryRow index := by
  have bound := index.isLt
  unfold binaryRow referenceBinaryRow shiftBinopRow
  simp only [logical_offset_1, logical_offset_2, logical_offset_3, logical_offset_4,
    logical_offset_5, logical_offset_6,
    show byteSignDataRegion.offset = 1 from rfl,
    show byteXorDataRegion.offset = 257 from rfl,
    show byteOrDataRegion.offset = 65793 from rfl,
    show byteAndDataRegion.offset = 131329 from rfl,
    show byteTruncateDataRegion.offset = 196865 from rfl,
    show byteShiftDataRegion.offset = 262401 from rfl]
  split_ifs with h0 h1 h2 h3 h4 h5
  · exact binary_region 0 (index.val) (by change index.val < 1; omega)
  · exact binary_region 1 (index.val - 1) (by change index.val - 1 < 256; omega)
  · exact binary_region 2 (index.val - 257) (by change index.val - 257 < 65536; omega)
  · exact binary_region 3 (index.val - 65793) (by change index.val - 65793 < 65536; omega)
  · exact binary_region 4 (index.val - 131329) (by change index.val - 131329 < 65536; omega)
  · exact binary_region 5 (index.val - 196865) (by change index.val - 196865 < 65536; omega)
  · exact binary_region 6 (index.val - 262401) (by change index.val - 262401 < 262144; omega)

private theorem rotation_lookup (mode : Fin 4) :
    (#[16, 12, 8, 7] : Array Nat)[mode.val]! = nativeRotations[mode] := by
  fin_cases mode <;> rfl

private theorem rotate_alias (mode : Fin 4) :
    nativeFixedData ⟨11 + mode.val, by have := mode.isLt; omega⟩ = rotateData mode := by
  have index : 11 + mode.val = mode.val + 11 := Nat.add_comm _ _
  simp only [nativeFixedData, rotateData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, index, Nat.add_succ, Nat.add_zero, List.getElem_cons_succ]

private theorem fixed_named (kind : Fin 15) (data : TableData 10)
    (named : nativeFixedData kind = data) (n : Nat) :
    nativeFixedRow kind n = data.columns.map (fun column => (column.get? n).getD 0) := by
  cases named
  rfl

/-- Actual XOR-rotate fields satisfy the unchanged 32-bit reference. -/
theorem rotateRow_eq_reference (index : Fin 262144) :
    rotateRow index = referenceRotateRow index := by
  let mode : Fin 4 := ⟨index.val / 65536, by have := index.isLt; omega⟩
  have same := rotate_alias mode
  have actual := imported_rotate_row mode (index.val % 65536) (Nat.mod_lt _ (by decide))
  unfold rotateRow nativeFixedRow
  rw [same, actual]
  unfold referenceRotateRow
  have first : index.val % 65536 / 256 = index.val / 256 % 256 := by omega
  have second : index.val % 65536 % 256 = index.val % 256 := by omega
  rw [first, second, rotation_lookup mode]

/-- All fixed contents are imported; the old relations are proved characterizations. -/
theorem fixedRow_eq_reference (index : Fin 1048961) :
    fixedRow index = referenceFixedRow index := by
  have bound := index.isLt
  unfold fixedRow referenceFixedRow
  simp only [logical_offset_7, logical_offset_8, logical_offset_9,
    logical_offset_10, logical_offset_11]
  split
  · exact binaryRow_eq_reference _
  · split
    · exact (fixed_named 7 nativeRegisterZeroData (by rfl) (index.val - 524545)).trans
        (imported_register_zero_row (index.val - 524545) (by omega))
    · split
      · exact (fixed_named 8 nativeSignData (by rfl) (index.val - 655617)).trans
          (Airbender.Setup.Proofs.unwrap_row _ (index.val - 655617) _
            (imported_sign_row (index.val - 655617) (by omega)))
      · split
        · exact (fixed_named 9 nativeCleanupData (by rfl) (index.val - 721153)).trans
            (imported_cleanup_row (index.val - 721153) (by omega))
        · split
          · exact (fixed_named 10 nativeConditionalData (by rfl) (index.val - 786689)).trans
              (imported_conditional_row ⟨index.val - 786689, by omega⟩)
          · exact rotateRow_eq_reference ⟨index.val - 786817, by omega⟩

/-- Arbitrary public starting states retain the original generic ROM interface. -/
theorem row_eq_reference (before : Reference.RiscV.Sail.State) (index : Fin 2097537) :
    row before index = referenceRow before index := by
  unfold row referenceRow
  split
  · exact fixedRow_eq_reference _
  · rfl

end Airbender.UnifiedReduced.Setup.Proofs
