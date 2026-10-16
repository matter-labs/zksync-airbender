import Airbender.Proofs.Keccak.ReferenceFixed
import Airbender.Proofs.Keccak.FixedCertificate
import Airbender.Proofs.Keccak.IotaCertificate
import Airbender.Proofs.Keccak.ImportedRotation
import Mathlib.Tactic.IntervalCases

namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem periodic_constant_get (count first n : Nat) (h : n < count * 256) :
    Block.get? (.periodic count 1 (Array.replicate 256 first)) n =
      some (first + n / 256) := by
  have hm : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_add, Int.natCast_ediv, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg (first + n / 256)) (Int.toNat_natCast (first + n / 256))

private theorem periodic_range_get (count n : Nat) (h : n < count * 256) :
    Block.get? (.periodic count 0 (Array.range 256)) n = some (n % 256) := by
  have hm : n % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_emod, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg (n % 256)) (Int.toNat_natCast (n % 256))

private theorem divided_key (n : Nat) (hn : n < 65536) :
    (Column.mk #[.affine 256 0 0,
      .periodic 255 1 (Array.replicate 256 1)]).get? n = some (n / 256) := by
  by_cases first : n < 256
  · simp [Column.get?, getFromBlocks, Block.get?, Block.length, first]
    omega
  · have rest : n - 256 < 255 * 256 := by omega
    simp only [Column.get?, getFromBlocks, Block.length,
      if_neg first, Array.size_replicate, if_pos rest]
    rw [periodic_constant_get _ _ _ rest]
    congr 1
    omega

private def byteData (kind : Fin 3) : TableData 8 := #v[xorData, iotaData, chiData][kind]
private def byteTag (kind : Fin 3) : Nat := #v[4, 38, 39][kind]
private def byteValue (kind : Fin 3) (n : Nat) : Nat :=
  if kind.val = 0 then n / 256 ^^^ n % 256
  else if kind.val = 1 then n % 256 ^^^ iotaByte (n / 256)
  else (n % 256 ^^^ 255) &&& (n / 256)

private theorem byte_length (kind : Fin 3) : (byteData kind).length = 65536 := by
  fin_cases kind <;> rfl

private theorem first_get (kind : Fin 3) (n : Nat) (hn : n < 65536) :
    (byteData kind).columns[0].get? n =
      some (if kind.val = 0 then n / 256 else n % 256) := by
  fin_cases kind
  · exact divided_key n hn
  · change (Column.mk #[.periodic 256 0 (Array.range 256)]).get? n = some (n % 256)
    simpa only [Column.get?, Array.toList, getFromBlocks, Block.length,
      Array.size_range, if_pos hn] using periodic_range_get 256 n hn
  · change (Column.mk #[.periodic 256 0 (Array.range 256)]).get? n = some (n % 256)
    simpa only [Column.get?, Array.toList, getFromBlocks, Block.length,
      Array.size_range, if_pos hn] using periodic_range_get 256 n hn

private theorem second_get (kind : Fin 3) (n : Nat) (hn : n < 65536) :
    (byteData kind).columns[1].get? n =
      some (if kind.val = 0 then n % 256 else n / 256) := by
  fin_cases kind
  · change (Column.mk #[.periodic 256 0 (Array.range 256)]).get? n = some (n % 256)
    simpa only [Column.get?, Array.toList, getFromBlocks, Block.length,
      Array.size_range, if_pos hn] using periodic_range_get 256 n hn
  · exact divided_key n hn
  · change (Column.mk #[.periodic 256 1 (Array.replicate 256 0)]).get? n = some (n / 256)
    simpa only [Column.get?, Array.toList, getFromBlocks, Block.length,
      Array.size_replicate, if_pos hn, Nat.zero_add] using periodic_constant_get 256 0 n hn

private theorem output_checks (kind : Fin 3) :
    checkBlocks (byteValue kind) 0 (byteData kind).columns[2].blocks.toList = true := by
  fin_cases kind
  · exact xor_output_checks
  · exact iota_output_checks
  · exact chi_output_checks

private theorem literal_size {α : Type*} (values : List α) :
    (Array.mk values).size = values.length := rfl

private theorem output_covered (kind : Fin 3) :
    (((byteData kind).columns[2]'(by decide)).blocks.toList.map Block.length).sum = 65536 := by
  fin_cases kind
  all_goals dsimp only [byteData, xorData, iotaData, chiData,
    Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [raw_toList_append, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Block.length,
    Array.size_ofFn, Array.size_replicate, Array.size_range,
    raw_size_append, literal_size, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul]

private theorem output_get (kind : Fin 3) (n : Nat) (hn : n < 65536) :
    (byteData kind).columns[2].get? n = some (byteValue kind n) := by
  have h := checkBlocks_sound _ _ 0 n (output_checks kind)
    (by simpa only [output_covered] using hn)
  simpa only [Column.get?, Nat.zero_add] using h

private theorem padding_get (kind : Fin 3) (j : Fin 4) (n : Nat) (hn : n < 65536) :
    (byteData kind).columns[j.val + 3].get? n = some 0 := by
  have column : (byteData kind).columns[j.val + 3] = Column.mk #[.affine 65536 0 0] := by
    fin_cases kind <;> fin_cases j <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

private theorem tag_get (kind : Fin 3) (n : Nat) (hn : n < 65536) :
    (byteData kind).columns[7].get? n = some (byteTag kind) := by
  have column : (byteData kind).columns[7] = Column.mk #[.affine 65536 (byteTag kind) 0] := by
    fin_cases kind <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

/-- Exact byte semantics, including the native key order, all padding columns
    and discriminator, proved from the actual imported rows. -/
theorem byte_region_reference (kind : Fin 3) (n : Nat) (hn : n < 65536) :
    fixedRow ⟨kind.val + 1, by omega⟩ n = byteRow (#v[4, 38, 39][kind]) n := by
  have data : fixedRow ⟨kind.val + 1, by omega⟩ n =
      (byteData kind).columns.map (fun column => (column.get? n).getD 0) := by
    fin_cases kind <;> rfl
  rw [data]
  apply Vector.ext
  intro j hj
  have first := first_get kind n hn
  have second := second_get kind n hn
  have output := output_get kind n hn
  have tag := tag_get kind n hn
  interval_cases j
  all_goals simp only [Vector.getElem_map, byteRow, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · rw [first]
    fin_cases kind <;> rfl
  · rw [second]
    fin_cases kind <;> rfl
  · rw [output]
    fin_cases kind <;> rfl
  · have zero : (byteData kind).columns[3].get? n = some 0 := padding_get kind 0 n hn
    simp only [zero, Option.getD_some]
  · have zero : (byteData kind).columns[4].get? n = some 0 := padding_get kind 1 n hn
    simp only [zero, Option.getD_some]
  · have zero : (byteData kind).columns[5].get? n = some 0 := padding_get kind 2 n hn
    simp only [zero, Option.getD_some]
  · have zero : (byteData kind).columns[6].get? n = some 0 := padding_get kind 3 n hn
    simp only [zero, Option.getD_some]
  · simp only [tag, Option.getD_some, byteTag]

private theorem affine_one_get (length first n : Nat) (hn : n < length) :
    Block.get? (.affine length first 1) n = some (first + n) := by
  simp [Block.get?, Block.length, hn]
  simpa only [Int.natCast_add] using
    And.intro (Int.natCast_nonneg (first + n)) (Int.toNat_natCast (first + n))

private theorem rotation_key_get (n : Nat) (hn : n < 1048576) :
    rotationData.columns[0].get? n = some n := by
  change (Column.mk #[.periodic 1 0 (Array.range 256),
    .affine 1048320 256 1]).get? n = some n
  by_cases first : n < 256
  · simp only [Column.get?, getFromBlocks, Block.length, Array.size_range,
      Nat.one_mul, if_pos first]
    rw [periodic_range_get 1 n first]
    congr 1
    omega
  · have rest : n - 256 < 1048320 := by omega
    simp only [Column.get?, getFromBlocks, Block.length, Array.size_range,
      Nat.one_mul, if_neg first, if_pos rest]
    rw [affine_one_get _ _ _ rest]
    congr 1
    omega

private theorem rotation_padding_get (j : Fin 4) (n : Nat) (hn : n < 1048576) :
    rotationData.columns[j.val + 3].get? n = some 0 := by
  have column : rotationData.columns[j.val + 3] = Column.mk #[.affine 1048576 0 0] := by
    fin_cases j <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

private theorem rotation_tag_get (n : Nat) (hn : n < 1048576) :
    rotationData.columns[7].get? n = some 40 := by
  change (Column.mk #[.affine 1048576 40 0]).get? n = some 40
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

/-- Both native rotation pieces for every packed 20-bit key. -/
theorem rotation_region_reference (n : Nat) (hn : n < 1048576) :
    fixedRow 4 n = rotationRow n := by
  have data : fixedRow 4 n =
      rotationData.columns.map (fun column => (column.get? n).getD 0) := rfl
  rw [data]
  let shift : Fin 16 := ⟨n / 65536, by omega⟩
  let word : Fin 65536 := ⟨n % 65536, Nat.mod_lt _ (by decide)⟩
  have reconstruct : 65536 * shift.val + word.val = n := by dsimp [shift, word]; omega
  have high := rotation_high_get shift word
  have low := rotation_low_get shift word
  rw [reconstruct] at high low
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, rotationRow]
  · simp only [rotation_key_get n hn, Option.getD_some]
  · simp only [high, Option.getD_some, shift, word]
  · simp only [low, Option.getD_some, shift, word]
  · have zero : rotationData.columns[3].get? n = some 0 := rotation_padding_get 0 n hn
    simp only [zero, Option.getD_some]
  · have zero : rotationData.columns[4].get? n = some 0 := rotation_padding_get 1 n hn
    simp only [zero, Option.getD_some]
  · have zero : rotationData.columns[5].get? n = some 0 := rotation_padding_get 2 n hn
    simp only [zero, Option.getD_some]
  · have zero : rotationData.columns[6].get? n = some 0 := rotation_padding_get 3 n hn
    simp only [zero, Option.getD_some]
  · simp only [rotation_tag_get n hn, Option.getD_some]

theorem zero_row_reference : fixedRow 0 0 = Vector.replicate 8 0 := by decide +kernel

/-- Recover the former mathematical characterization without restricting the
    supplied controller or assuming table correspondence. -/
theorem setup_row_characterization (control : Fin 4096 → Vector Nat 6) (index : Fin 1249281) :
    setupRow control index = referenceSetupRow control index := by
  have bound := index.isLt
  unfold setupRow referenceSetupRow
  dsimp only [zeroDataRegion, xorDataRegion, controllerDataRegion, iotaDataRegion,
    chiDataRegion, rotationDataRegion, rotationRawDataRegion]
  split_ifs
  · have zero : index.val = 0 := by assumption
    simpa only [zero, Nat.sub_zero] using zero_row_reference
  · exact byte_region_reference 0 _ (by omega)
  · rfl
  · exact byte_region_reference 1 _ (by omega)
  · exact byte_region_reference 2 _ (by omega)
  · exact rotation_region_reference _ (by omega)

/-- Canonical imported values and the signed circuit lift agree in the native
    field. Existing generic-field lookup consequences keep their field scope. -/
theorem fixed_region_native_cast (kind : Fin 5) (index : Fin (fixedData kind).length) :
    (fixedRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((fixedData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus)) := by
  have offset : (fixedData kind).offset = 0 := by fin_cases kind <;> rfl
  apply Vector.ext
  intro j hj
  simp [fixedRow, TableData.row, offset, signedValue_cast]

end Airbender.Keccak.Proofs
