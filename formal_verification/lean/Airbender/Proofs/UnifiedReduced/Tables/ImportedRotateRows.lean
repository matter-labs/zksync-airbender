import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate16
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate12Low
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate12High
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate8
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate7Low
import Airbender.Proofs.UnifiedReduced.Tables.ImportedRotate7High
import Airbender.Proofs.UnifiedReduced.Tables.RotateReferenceBytes
import Airbender.Proofs.UnifiedReduced.Tables.ImportedWideKeys
import Airbender.Proofs.Tables.ShiftXorCertificate
import Airbender.Proofs.Tables.ImportedBinaryRows
import Airbender.Proofs.Tables.LiteralSizes

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

noncomputable def rotateData (mode : Fin 4) : TableData 10 :=
  #v[nativeRotate16Data, nativeRotate12Data, nativeRotate8Data, nativeRotate7Data][mode]

private theorem first_shape (mode : Fin 4) : (rotateData mode).columns[0] =
    Column.mk #[.periodic 256 1 (Array.replicate 256 0)] := by
  fin_cases mode <;> rfl

private theorem first (mode : Fin 4) (n : Nat) (bound : n < 65536) :
    (rotateData mode).columns[0].get? n = some (n / 256) := by
  have shape := first_shape mode
  have actual : (Column.mk #[.periodic 256 1 (Array.replicate 256 0)]).get? n =
      some (n / 256) := by
    change getFromBlocks [.periodic 256 1 (Array.replicate 256 0)] n = _
    simp only [getFromBlocks, Block.length, Array.size_replicate,
      Nat.reduceMul, if_pos bound]
    exact (BinaryColumns.periodic_constant 256 0 n bound).trans (by simp only [Nat.zero_add])
  exact (congrArg (fun column : Column => column.get? n) shape).trans actual

private def secondKind (mode : Fin 4) : Fin 3 := if mode.val = 0 then 0 else 1

private def secondColumn (kind : Fin 3) : Column := Column.mk #[
  if kind.val = 0 then .affine 1 0 0 else .dense (Array.replicate 1 0),
  .periodic 255 0 (Array.ofFn (fun i : Fin 256 => (1 + i.val) % 256)),
  .dense (Array.ofFn (fun i : Fin 255 => 1 + i.val))]

private theorem second_shape (mode : Fin 4) :
    (rotateData mode).columns[1] = secondColumn (secondKind mode) := by
  fin_cases mode <;> rfl

private theorem second_wide_shape (kind : Fin 3) :
    (wideData kind).columns[1] = secondColumn kind := by
  fin_cases kind <;> rfl

private theorem second (mode : Fin 4) (n : Nat) (bound : n < 65536) :
    (rotateData mode).columns[1].get? n = some (n % 256) := by
  have actual := congrArg (fun column : Column => column.get? n) (second_shape mode)
  have ordinary := congrArg (fun column : Column => column.get? n) (second_wide_shape (secondKind mode))
  exact actual.trans (ordinary.symm.trans (wide_second_key (secondKind mode) n bound))

private theorem constant_get (length value n : Nat) (bound : n < length) :
    (Column.mk #[.affine length value 0]).get? n = some value := by
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

private theorem output_extent12 :
    ((nativeRotate12Data.columns[4]).blocks.toList.map Block.length).sum = 65536 := by
  dsimp only [nativeRotate12Data, Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Block.length, raw_literal_size,
    List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceMul]

private theorem output_extent8 :
    ((nativeRotate8Data.columns[5]).blocks.toList.map Block.length).sum = 65536 := by
  dsimp only [nativeRotate8Data, Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Block.length, raw_literal_size,
    List.length_cons, List.length_nil, Array.size_ofFn,
     raw_size_append, Nat.reduceAdd, Nat.reduceMul]

private theorem output_extent7 :
    ((nativeRotate7Data.columns[5]).blocks.toList.map Block.length).sum = 65536 := by
  dsimp only [nativeRotate7Data, Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Block.length, raw_literal_size,
    List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceMul]

private abbrev nonzeroLane (mode lane : Fin 4) : Prop :=
  (mode.val = 0 ∧ lane.val = 2) ∨
  (mode.val = 1 ∧ (lane.val = 2 ∨ lane.val = 3)) ∨
  (mode.val = 2 ∧ lane.val = 3) ∨
  (mode.val = 3 ∧ (lane.val = 0 ∨ lane.val = 3))

private theorem zero_column (mode lane : Fin 4) (zero : ¬ nonzeroLane mode lane) :
    (rotateData mode).columns[lane.val + 2] = Column.mk #[.affine 65536 0 0] := by
  fin_cases mode <;> fin_cases lane
  · rfl
  · rfl
  · exact False.elim (zero (by decide))
  · rfl
  · rfl
  · rfl
  · exact False.elim (zero (by decide))
  · exact False.elim (zero (by decide))
  · rfl
  · rfl
  · rfl
  · exact False.elim (zero (by decide))
  · exact False.elim (zero (by decide))
  · rfl
  · rfl
  · exact False.elim (zero (by decide))

private theorem zero_output (mode lane : Fin 4) (zero : ¬ nonzeroLane mode lane)
    (n : Nat) (bound : n < 65536) :
    (rotateData mode).columns[lane.val + 2].get? n = some 0 := by
  exact (congrArg (fun column : Column => column.get? n) (zero_column mode lane zero)).trans
    (constant_get 65536 0 n bound)

private theorem output (mode lane : Fin 4) (n : Nat) (bound : n < 65536) :
    (rotateData mode).columns[lane.val + 2].get? n =
      some (finiteRotatedByte mode lane (n / 256 ^^^ n % 256)) := by
  fin_cases mode <;> fin_cases lane
  · exact zero_output 0 0 (by decide) n bound
  · exact zero_output 0 1 (by decide) n bound
  · have extent : (byteXorData.columns[2].blocks.toList.map Block.length).sum = 65536 :=
      BinaryColumns.coverage 0
    have actual := checkBlocks_sound _ _ 0 n ShiftCertificate.xor_outputs
      (by rw [extent]; exact bound)
    have values : byteXorData.columns[2].get? n = some (n / 256 ^^^ n % 256) := by
      simpa only [Column.get?, Nat.zero_add] using actual
    exact (congrArg (fun column : Column => column.get? n) imported_rotate16_xor).trans values
  · exact zero_output 0 3 (by decide) n bound
  · exact zero_output 1 0 (by decide) n bound
  · exact zero_output 1 1 (by decide) n bound
  · have actual := checkBlocks_sound _ _ 0 n imported_rotate12low_output
      (by rw [output_extent12]; exact bound)
    simpa [Column.get?, finiteRotatedByte, rotateData] using actual
  · exact imported_rotate12high_output n bound
  · exact zero_output 2 0 (by decide) n bound
  · exact zero_output 2 1 (by decide) n bound
  · exact zero_output 2 2 (by decide) n bound
  · have actual := checkBlocks_sound _ _ 0 n imported_rotate8_output
      (by rw [output_extent8]; exact bound)
    simpa [Column.get?, finiteRotatedByte, rotateData] using actual
  · exact imported_rotate7high_output n bound
  · exact zero_output 3 1 (by decide) n bound
  · exact zero_output 3 2 (by decide) n bound
  · have actual := checkBlocks_sound _ _ 0 n imported_rotate7low_output
      (by rw [output_extent7]; exact bound)
    simpa [Column.get?, finiteRotatedByte, rotateData] using actual

private theorem padding (mode : Fin 4) (lane : Fin 3) (n : Nat) (bound : n < 65536) :
    (rotateData mode).columns[lane.val + 6].get? n = some 0 := by
  have shape : (rotateData mode).columns[lane.val + 6] = Column.mk #[.affine 65536 0 0] := by
    fin_cases mode <;> fin_cases lane <;> rfl
  exact (congrArg (fun column : Column => column.get? n) shape).trans (constant_get 65536 0 n bound)

private theorem tag (mode : Fin 4) (n : Nat) (bound : n < 65536) :
    (rotateData mode).columns[9].get? n = some (47 + mode.val) := by
  have shape : (rotateData mode).columns[9] = Column.mk #[.affine 65536 (47 + mode.val) 0] := by
    fin_cases mode <;> rfl
  exact (congrArg (fun column : Column => column.get? n) shape).trans (constant_get 65536 _ n bound)

/-- Every physical rotation field is read from the selected native artifact. -/
theorem imported_rotate_row (mode : Fin 4) (n : Nat) (bound : n < 65536) :
    (rotateData mode).columns.map (fun column => (column.get? n).getD 0) =
      let out := ((BitVec.ofNat 32 (n / 256 ^^^ n % 256)).rotateRight nativeRotations[mode]).toNat
      #v[n / 256, n % 256, out % 256, out / 256 % 256,
        out / 65536 % 256, out / 16777216 % 256, 0, 0, 0, 47 + mode.val] := by
  have xor_bound : n / 256 ^^^ n % 256 < 256 :=
    Nat.xor_lt_two_pow (n := 8) (by omega) (Nat.mod_lt _ (by decide))
  have reference (lane : Fin 4) := rotated_byte_reference mode lane
    ⟨n / 256 ^^^ n % 256, xor_bound⟩
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · exact congrArg (fun value => value.getD 0) (first mode n bound)
  · exact congrArg (fun value => value.getD 0) (second mode n bound)
  · have value := output mode 0 n bound
    rw [← reference 0] at value
    simpa [referenceRotatedByte] using congrArg (fun item => item.getD 0) value
  · have value := output mode 1 n bound
    rw [← reference 1] at value
    simpa [referenceRotatedByte] using congrArg (fun item => item.getD 0) value
  · have value := output mode 2 n bound
    rw [← reference 2] at value
    simpa [referenceRotatedByte] using congrArg (fun item => item.getD 0) value
  · have value := output mode 3 n bound
    rw [← reference 3] at value
    simpa [referenceRotatedByte] using congrArg (fun item => item.getD 0) value
  · exact congrArg (fun value => value.getD 0) (padding mode 0 n bound)
  · exact congrArg (fun value => value.getD 0) (padding mode 1 n bound)
  · exact congrArg (fun value => value.getD 0) (padding mode 2 n bound)
  · exact congrArg (fun value => value.getD 0) (tag mode n bound)

end Airbender.UnifiedReduced.Setup.Proofs
