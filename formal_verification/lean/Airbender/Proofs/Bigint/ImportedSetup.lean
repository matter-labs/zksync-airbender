import Airbender.Review.Circuits.Bigint.Tables.Setup
set_option Elab.async false
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
private theorem take_block (block : Block) (rest : List Block) (n length : Nat)
    (size : block.length = length) (bound : n < length) :
    getFromBlocks (block :: rest) n = block.get? n := by
  rw [getFromBlocks, size, if_pos bound]

private theorem skip_block (block : Block) (rest : List Block) (n length : Nat)
    (size : block.length = length) (bound : ¬n < length) :
    getFromBlocks (block :: rest) n = getFromBlocks rest (n - length) := by
  rw [getFromBlocks, size, if_neg bound]

private theorem column_get_array (blocks : Array Block) (n : Nat) :
    (Column.mk blocks).get? n = getFromBlocks blocks.toList n := rfl

private theorem blocks_to_list (b0 b1 b2 b3 b4 b5 : Block) :
    (#[b0, b1, b2, b3, b4, b5] : Array Block).toList = [b0, b1, b2, b3, b4, b5] := rfl

private theorem range_block_length (count width : Nat) :
    (Block.periodic count 0 (Array.range width)).length = count * width := by
  simp only [Block.length, Array.size_range]

private theorem function_block_length (count width : Nat) (values : Fin width → Nat) :
    (Block.periodic count 0 (Array.ofFn values)).length = count * width := by
  simp only [Block.length, Array.size_ofFn]

private theorem second_column : (importedSetup.columns[1]'(by decide)) = Column.mk #[
    .periodic 513 0 (Array.range 512),
    .periodic 1023 0 (Array.ofFn (fun i : Fin 1024 => (512 + i.val) % 1024)),
    .affine 512 512 1, .affine 14337 0 0,
    .periodic 256 0 (Array.ofFn (fun i : Fin 256 => (1 + i.val) % 256)),
    .affine 2803711 0 0] := by rfl

private theorem offset_lt (n base limit : Nat) (lower : base ≤ n) (upper : n < limit) :
    n - base < limit - base := by omega

private theorem offset_not_lt (n base limit : Nat) (lower : ¬n < limit) :
    ¬n - base < limit - base :=
  Nat.not_lt_of_ge (Nat.sub_le_sub_right (Nat.le_of_not_gt lower) base)

private theorem physical_blocks (b0 b1 b2 b3 b4 b5 : Block)
    (s0 : b0.length = 262656) (s1 : b1.length = 1047552)
    (s2 : b2.length = 512) (s3 : b3.length = 14337) (s4 : b4.length = 65536)
    (g0 : ∀ n, n < 262656 → b0.get? n = some (n % 512))
    (g1 : ∀ n, n < 1047552 → b1.get? n = some ((512 + n % 1024) % 1024))
    (g2 : ∀ n, n < 512 → b2.get? n = some (512 + n))
    (g3 : ∀ n, n < 14337 → b3.get? n = some 0)
    (g4 : ∀ n, n < 65536 → b4.get? n = some ((1 + n % 256) % 256))
    (n : Nat) (hn : n < 1390592) :
    getFromBlocks [b0, b1, b2, b3, b4, b5] n = some (
      if n < 262656 then n % 512
      else if n < 1310208 then (512 + (n - 262656) % 1024) % 1024
      else if n < 1310720 then 512 + (n - 1310208)
      else if n < 1325057 then 0 else (1 + (n - 1325057) % 256) % 256) := by
  by_cases h0 : n < 262656
  · rw [take_block b0 _ n 262656 s0 h0, if_pos h0]
    exact g0 n h0
  rw [skip_block b0 _ n 262656 s0 h0, if_neg h0]
  by_cases h1 : n < 1310208
  · have current : n - 262656 < 1047552 := offset_lt n 262656 1310208 (Nat.le_of_not_gt h0) h1
    rw [take_block b1 _ (n - 262656) 1047552 s1 current, if_pos h1]
    exact g1 (n - 262656) current
  have previous : ¬n - 262656 < 1047552 := offset_not_lt n 262656 1310208 h1
  rw [skip_block b1 _ (n - 262656) 1047552 s1 previous, if_neg h1]
  rw [Nat.sub_sub]
  by_cases h2 : n < 1310720
  · have current : n - 1310208 < 512 := offset_lt n 1310208 1310720 (Nat.le_of_not_gt h1) h2
    rw [take_block b2 _ (n - 1310208) 512 s2 current, if_pos h2]
    exact g2 (n - 1310208) current
  have previous' : ¬n - 1310208 < 512 := offset_not_lt n 1310208 1310720 h2
  rw [skip_block b2 _ (n - 1310208) 512 s2 previous', if_neg h2]
  rw [Nat.sub_sub]
  by_cases h3 : n < 1325057
  · have current : n - 1310720 < 14337 := offset_lt n 1310720 1325057 (Nat.le_of_not_gt h2) h3
    rw [take_block b3 _ (n - 1310720) 14337 s3 current, if_pos h3]
    exact g3 (n - 1310720) current
  have previous'' : ¬n - 1310720 < 14337 := offset_not_lt n 1310720 1325057 h3
  rw [skip_block b3 _ (n - 1310720) 14337 s3 previous'', if_neg h3]
  rw [Nat.sub_sub]
  have current : n - 1325057 < 65536 := offset_lt n 1325057 1390593 (Nat.le_of_not_gt h3)
    (Nat.lt_trans hn (by decide))
  rw [take_block b4 _ (n - 1325057) 65536 s4 current]
  exact g4 (n - 1325057) current


private theorem second_physical (n : Nat) (hn : n < 1390592) :
    (importedSetup.columns[1]).get? n = some (
      if n < 262656 then n % 512
      else if n < 1310208 then (512 + (n - 262656) % 1024) % 1024
      else if n < 1310720 then 512 + (n - 1310208)
      else if n < 1325057 then 0 else (1 + (n - 1325057) % 256) % 256) := by
  rw [second_column, column_get_array, blocks_to_list]
  exact physical_blocks
    (.periodic 513 0 (Array.range 512))
    (.periodic 1023 0 (Array.ofFn (fun i : Fin 1024 => (512 + i.val) % 1024)))
    (.affine 512 512 1) (.affine 14337 0 0)
    (.periodic 256 0 (Array.ofFn (fun i : Fin 256 => (1 + i.val) % 256)))
    (.affine 2803711 0 0)
    (range_block_length 513 512)
    (function_block_length 1023 1024 (fun i => (512 + i.val) % 1024))
    rfl rfl (function_block_length 256 256 (fun i => (1 + i.val) % 256))
    (fun m bound => periodic_range_get 512 513 m (by decide) bound)
    (fun m bound => periodic_cyclic_get 1024 1023 512 m (by decide) bound)
    (fun m bound => affine_start_get 512 512 m bound)
    (fun m bound => affine_const_get 14337 0 m bound)
    (fun m bound => periodic_cyclic_get 256 256 1 m (by decide) bound)
    n hn


private theorem mod_decomposition (n modulus quotient remainder : Nat)
    (equal : n = modulus * quotient + remainder) (small : remainder < modulus) :
    n % modulus = remainder := by
  rw [equal, Nat.mul_add_mod, Nat.mod_eq_of_lt small]

private theorem second_get (n : Nat) (hn : n < 1390592) :
    (importedSetup.columns[1]).get? n = some (
      if n < 262144 then n % 512
      else if n < 1310720 then (n - 262144) % 1024
      else if n < 1325056 then 0 else (n - 1325056) % 256) := by
  rw [second_physical n hn]
  simp only [Nat.add_mod_mod]
  by_cases h0 : n < 262144
  · simp only [if_pos h0, if_pos (show n < 262656 by omega)]
  by_cases h1 : n < 262656
  · have small : n - 262144 < 512 := by omega
    have value := mod_decomposition n 512 512 (n - 262144) (by omega) small
    simp only [if_neg h0, if_pos h1, if_pos (show n < 1310720 by omega), value,
      Nat.mod_eq_of_lt (show n - 262144 < 1024 by omega)]
  by_cases h2 : n < 1310208
  · have same : 512 + (n - 262656) = n - 262144 := by omega
    simp only [if_neg h0, if_neg h1, if_pos h2,
      if_pos (show n < 1310720 by omega), same]
  by_cases h3 : n < 1310720
  · have value := mod_decomposition (n - 262144) 1024 1023
      (512 + (n - 1310208)) (by omega) (by omega)
    simp only [if_neg h0, if_neg h1, if_neg h2, if_pos h3, value]
  by_cases h4 : n < 1325056
  · simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
      if_pos (show n < 1325057 by omega)]
  by_cases edge : n = 1325056
  · subst n
    norm_num
  · have same : 1 + (n - 1325057) = n - 1325056 := by omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
      if_neg (show ¬n < 1325057 by omega), same]

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
