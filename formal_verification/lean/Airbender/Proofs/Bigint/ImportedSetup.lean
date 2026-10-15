import Airbender.Review.Circuits.Bigint.Tables.Setup
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open Airbender.Setup
namespace Airbender.Bigint.Proofs
set_option warningAsError true
private theorem periodic_constant_get (b count n : Nat) (hb : 0 < b) (h : n < count * b) :
    Block.get? (.periodic count 1 (Array.replicate b 0)) n = some (n / b) := by
  have hm : n % b < b := Nat.mod_lt _ hb
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_ediv] using
    And.intro (Int.natCast_nonneg (n / b)) (Int.toNat_natCast (n / b))
private theorem periodic_range_get (b count n : Nat) (hb : 0 < b) (h : n < count * b) :
    Block.get? (.periodic count 0 (Array.range b)) n = some (n % b) := by
  have hm : n % b < b := Nat.mod_lt _ hb
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_emod] using
    And.intro (Int.natCast_nonneg (n % b)) (Int.toNat_natCast (n % b))
private theorem periodic_cyclic_get (b count first n : Nat) (hb : 0 < b) (h : n < count * b) :
    Block.get? (.periodic count 0 (Array.ofFn (fun i : Fin b => (first + i.val) % b))) n =
      some ((first + n % b) % b) := by
  have hm : n % b < b := Nat.mod_lt _ hb
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_emod, Int.natCast_add] using
    And.intro (Int.natCast_nonneg ((first + n) % b)) (Int.toNat_natCast ((first + n) % b))
private theorem affine_one_get (b n : Nat) (h : n < b) :
    Block.get? (.affine b 0 1) n = some n := by simp [Block.get?, Block.length, h]
private theorem affine_const_get (b first n : Nat) (h : n < b) :
    Block.get? (.affine b first 0) n = some first := by simp [Block.get?, Block.length, h]

private theorem first_get (n : Nat) (hn : n < 1390592) :
    (importedSetup.columns[0]).get? n = some (
      if n < 262144 then n / 512
      else if n < 1310720 then (n - 262144) / 1024
      else if n < 1312768 then n - 1310720
      else if n < 1316864 then n - 1312768
      else if n < 1325056 then n - 1316864
      else n - 1325056) := by
  have column : (importedSetup.columns[0]'(by decide)) = Column.mk #[
      .periodic 512 1 (Array.replicate 512 0),
      .periodic 1024 1 (Array.replicate 1024 0),
      .affine 2048 0 1, .affine 4096 0 1, .affine 8192 0 1,
      .affine 65536 0 1, .affine 2803712 0 0] := by rfl
  rw [column]
  clear column
  split_ifs
  all_goals simp (disch := omega) [*, Column.get?, getFromBlocks, Block.length,
    periodic_constant_get, affine_one_get, Nat.sub_sub]
  all_goals (try split_ifs) <;> (try simp_all) <;> omega

private theorem affine_start_get (b first n : Nat) (h : n < b) :
    Block.get? (.affine b first 1) n = some (first + n) := by
  simp [Block.get?, Block.length, h]
  simpa only [Int.natCast_add] using
    And.intro (Int.natCast_nonneg (first + n)) (Int.toNat_natCast (first + n))
private theorem second_get (n : Nat) (hn : n < 1390592) :
    (importedSetup.columns[1]).get? n = some (
      if n < 262144 then n % 512
      else if n < 1310720 then (n - 262144) % 1024
      else if n < 1325056 then 0 else (n - 1325056) % 256) := by
  have column : (importedSetup.columns[1]'(by decide)) = Column.mk #[
    .periodic 513 0 (Array.range 512),
    .periodic 1023 0 (Array.ofFn (fun i : Fin 1024 => (512 + i.val) % 1024)),
    .affine 512 512 1, .affine 14337 0 0,
    .periodic 256 0 (Array.ofFn (fun i : Fin 256 => (1 + i.val) % 256)),
    .affine 2803711 0 0] := by rfl
  rw [column]
  clear column
  split_ifs
  all_goals simp (disch := omega) [*, Column.get?, getFromBlocks, Block.length,
    periodic_range_get, periodic_cyclic_get, affine_start_get, affine_const_get, Nat.sub_sub]
  all_goals (try split_ifs) <;> (try simp_all) <;> omega
private theorem tag_get (n : Nat) (hn : n < 1390592) :
    (importedSetup.columns[2]).get? n = some (
      if n < 262144 then 22 else if n < 1310720 then 23
      else if n < 1312768 then 24 else if n < 1316864 then 25
      else if n < 1325056 then 26 else 41) := by
  have column : (importedSetup.columns[2]'(by decide)) = Column.mk #[
    .affine 262144 22 0, .affine 1048576 23 0, .affine 2048 24 0,
    .affine 4096 25 0, .affine 8192 26 0, .affine 65536 41 0,
    .affine 2803712 0 0] := by rfl
  rw [column]
  clear column
  split_ifs
  all_goals simp (disch := omega) [*, Column.get?, getFromBlocks, Block.length,
    affine_const_get, Nat.sub_sub]
  all_goals (try split_ifs) <;> (try simp_all) <;> omega

theorem setup_row_characterization (index : Fin 1390592) :
    setupRow index =
      if index.val < 262144 then (index.val / 512, index.val % 512, 22)
      else if index.val < 1310720 then ((index.val - 262144) / 1024, (index.val - 262144) % 1024, 23)
      else if index.val < 1312768 then (index.val - 1310720, 0, 24)
      else if index.val < 1316864 then (index.val - 1312768, 0, 25)
      else if index.val < 1325056 then (index.val - 1316864, 0, 26)
      else (index.val - 1325056, (index.val - 1325056) % 256, 41) := by
  change (((importedSetup.columns[0]).get? index.val).getD 0,
    ((importedSetup.columns[1]).get? index.val).getD 0,
    ((importedSetup.columns[2]).get? index.val).getD 0) = _
  simp only [first_get _ index.isLt, second_get _ index.isLt, tag_get _ index.isLt]
  simp only [Option.getD_some]
  by_cases h0 : index.val < 262144
  · simp [h0]
  by_cases h1 : index.val < 1310720
  · simp [h0, h1]
  by_cases h2 : index.val < 1312768
  · have low : index.val < 1325056 := by omega
    simp [h0, h1, h2, low]
  by_cases h3 : index.val < 1316864
  · have low : index.val < 1325056 := by omega
    simp [h0, h1, h2, h3, low]
  by_cases h4 : index.val < 1325056
  · simp [h0, h1, h2, h3, h4]
  · simp [h0, h1, h2, h3, h4]

theorem setup_row_native_cast (index : Fin 1390592) :
    #v[((setupRow index).1 : ZMod babyBearModulus),
      ((setupRow index).2.1 : ZMod babyBearModulus),
      ((setupRow index).2.2 : ZMod babyBearModulus)] =
      (importedSetup.row index).map (fun (value : Int) => (value : ZMod babyBearModulus)) := by
  have offset : importedSetup.offset = 0 := by rfl
  apply Vector.ext
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals simp [setupRow, TableData.row, signedValue_cast, offset]

theorem setup_lookup_native_iff [Fact babyBearModulus.Prime]
    (entry : Vector (Expression (ZMod babyBearModulus)) 3)
    (env : Environment (ZMod babyBearModulus)) :
    (Lookup.mk setupTable.toRaw entry).Contains env ↔
      (Lookup.mk (importedSetup.table "Airbender.Bigint.Native").toRaw entry).Contains env := by
  change (∃ i : Fin 1390592, entry.map (Expression.eval env) =
    #v[((setupRow i).1 : ZMod babyBearModulus), ((setupRow i).2.1 : ZMod babyBearModulus),
      ((setupRow i).2.2 : ZMod babyBearModulus)]) ↔
    ∃ i : Fin importedSetup.length, entry.map (Expression.eval env) =
      (importedSetup.row i).map (fun (value : Int) => (value : ZMod babyBearModulus))
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, h.trans (setup_row_native_cast i)⟩
  · rintro ⟨i, h⟩
    exact ⟨i, h.trans (setup_row_native_cast i).symm⟩

end Airbender.Bigint.Proofs
