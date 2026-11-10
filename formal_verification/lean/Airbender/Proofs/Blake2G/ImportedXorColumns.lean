import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Proofs.Blake2G.XorCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2G.Proofs.XorColumns
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/- Check native column reads once, separately from their public row assembly. -/
def chunkSize (kind : Fin 5) : Nat := 2 ^ (#v[8, 3, 4, 7, 9][kind])
def chunkTag (kind : Fin 5) : Nat := #v[4, 17, 18, 19, 20][kind]

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
private theorem affine_get (length first n : Nat) (hn : n < length) :
    Block.get? (.affine length first 1) n = some (first + n) := by
  simp [Block.get?, Block.length, hn]
  simpa only [Int.natCast_add] using
    And.intro (Int.natCast_nonneg (first + n)) (Int.toNat_natCast (first + n))
private theorem dense_range_get (length n : Nat) (hn : n < length) :
    Block.get? (.dense (Array.range length)) n = some n := by
  simp [Block.get?, Block.length, hn]
private theorem dense_affine_get (length first n : Nat) (hn : n < length) :
    Block.get? (.dense (Array.ofFn (fun i : Fin length => first + i.val))) n =
      some (first + n) := by
  simp [Block.get?, Block.length, hn]

private theorem native_length (kind : Fin 5) :
    (xorData kind).length = chunkSize kind * chunkSize kind := by
  fin_cases kind <;> rfl

theorem first_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[0].get? n = some (n / chunkSize kind) := by
  have columns : (xorData kind).columns[0] = Column.mk #[
      .periodic (chunkSize kind) 1 (Array.replicate (chunkSize kind) 0)] := by
    fin_cases kind <;> rfl
  rw [columns]
  have positive : 0 < chunkSize kind := by fin_cases kind <;> decide
  simpa only [Column.get?, Array.toList, getFromBlocks, Block.length,
    Array.size_replicate, if_pos (native_length kind ▸ hn)] using
    periodic_constant_get _ _ n positive (native_length kind ▸ hn)

private theorem offset_add (n offset : Nat) (lower : offset ≤ n) :
    offset + (n - offset) = n := by omega

private theorem xor9_tail_bound (n : Nat) (upper : n < 262144) :
    n - 8 - 261632 < 504 := by omega

private theorem xor9_tail_mod (n : Nat) (upper : n < 262144)
    (lower : ¬n - 8 < 261632) : 8 + (n - 261640) = n % 512 := by
  have split : n = 512 * 511 + (8 + (n - 261640)) := by omega
  have small : 8 + (n - 261640) < 512 := by omega
  have equal := congrArg (fun value => value % 512) split
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt small] at equal
  exact equal.symm

private theorem take_input_block (block : Block) (rest : List Block) (n length : Nat)
    (size : block.length = length) (bound : n < length) :
    getFromBlocks (block :: rest) n = block.get? n := by
  rw [getFromBlocks, size, if_pos bound]

private theorem skip_input_block (block : Block) (rest : List Block) (n length : Nat)
    (size : block.length = length) (bound : ¬n < length) :
    getFromBlocks (block :: rest) n = getFromBlocks rest (n - length) := by
  rw [getFromBlocks, size, if_neg bound]

private theorem column_get_three (leading middle tail : Block) (n : Nat) :
    (Column.mk #[leading, middle, tail]).get? n = getFromBlocks [leading, middle, tail] n := rfl

private theorem input_function_length (count width : Nat) (values : Fin width → Nat) :
    (Block.periodic count 0 (Array.ofFn values)).length = count * width := by
  simp only [Block.length, Array.size_ofFn]

private theorem xor9_input_blocks (leading middle tail : Block)
    (s0 : leading.length = 8) (s1 : middle.length = 261632) (s2 : tail.length = 504)
    (g0 : ∀ n, n < 8 → leading.get? n = some n)
    (g1 : ∀ n, n < 261632 → middle.get? n = some ((8 + n % 512) % 512))
    (g2 : ∀ n, n < 504 → tail.get? n = some (8 + n))
    (n : Nat) (upper : n < 262144) :
    getFromBlocks [leading, middle, tail] n = some (n % 512) := by
  by_cases h0 : n < 8
  · rw [take_input_block leading _ n 8 s0 h0, g0 n h0,
      Nat.mod_eq_of_lt (lt_trans h0 (by decide : 8 < 512))]
  rw [skip_input_block leading _ n 8 s0 h0]
  by_cases h1 : n - 8 < 261632
  · rw [take_input_block middle _ (n - 8) 261632 s1 h1, g1 (n - 8) h1,
      Nat.add_mod_mod, offset_add n 8 (Nat.le_of_not_gt h0)]
  rw [skip_input_block middle _ (n - 8) 261632 s1 h1]
  have bound := xor9_tail_bound n upper
  rw [take_input_block tail [] (n - 8 - 261632) 504 s2 bound,
    g2 (n - 8 - 261632) bound, Nat.sub_sub]
  exact congrArg some (xor9_tail_mod n upper h1)

private theorem xor9_second (n : Nat) (upper : n < 262144) :
    (Column.mk #[.dense (Array.range 8),
      .periodic 511 0 (Array.ofFn (fun i : Fin 512 => (8 + i.val) % 512)),
      .affine 504 8 1]).get? n = some (n % 512) := by
  rw [column_get_three]
  exact xor9_input_blocks (.dense (Array.range 8))
    (.periodic 511 0 (Array.ofFn (fun i : Fin 512 => (8 + i.val) % 512)))
    (.affine 504 8 1) rfl (input_function_length 511 512 (fun i => (8 + i.val) % 512)) rfl
    (fun m bound => dense_range_get 8 m bound)
    (fun m bound => periodic_cyclic_get 512 511 8 m (by decide) bound)
    (fun m bound => affine_get 504 8 m bound) n upper

private def secondColumn (kind : Fin 5) : Column :=
  #v[Column.mk #[.periodic 256 0 (Array.range 256)],
    Column.mk #[.periodic 8 0 (Array.range 8)],
    Column.mk #[.periodic 1 0 (Array.range 8),
      .periodic 15 0 (Array.ofFn (fun i : Fin 16 => (8 + i.val) % 16)),
      .dense (Array.ofFn (fun i : Fin 8 => 8 + i.val))],
    Column.mk #[.dense (Array.range 8),
      .periodic 127 0 (Array.ofFn (fun i : Fin 128 => (8 + i.val) % 128)),
      .dense (Array.ofFn (fun i : Fin 120 => 8 + i.val))],
    Column.mk #[.dense (Array.range 8),
      .periodic 511 0 (Array.ofFn (fun i : Fin 512 => (8 + i.val) % 512)),
      .affine 504 8 1]][kind]

private theorem second_column_shape (kind : Fin 5) :
    (xorData kind).columns[1] = secondColumn kind := by
  fin_cases kind <;> rfl

theorem second_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[1].get? n = some (n % chunkSize kind) := by
  rw [second_column_shape]
  rw [native_length] at hn
  fin_cases kind
  · change (Column.mk #[.periodic 256 0 (Array.range 256)]).get? n = some (n % 256)
    change n < 65536 at hn
    simp [Column.get?, getFromBlocks, Block.length, periodic_range_get, hn]
  · change (Column.mk #[.periodic 8 0 (Array.range 8)]).get? n = some (n % 8)
    change n < 64 at hn
    simp [Column.get?, getFromBlocks, Block.length, periodic_range_get, hn]
  · change (Column.mk #[.periodic 1 0 (Array.range 8),
      .periodic 15 0 (Array.ofFn (fun i : Fin 16 => (8 + i.val) % 16)),
      .dense (Array.ofFn (fun i : Fin 8 => 8 + i.val))]).get? n = some (n % 16)
    change n < 256 at hn
    by_cases h0 : n < 8
    · simp [Column.get?, getFromBlocks, Block.length, periodic_range_get, h0]
      omega
    · by_cases h1 : n - 8 < 240
      · simp [Column.get?, getFromBlocks, Block.length, periodic_cyclic_get, h0, h1]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, h1,
          dense_affine_get]
        omega
  · change (Column.mk #[.dense (Array.range 8),
      .periodic 127 0 (Array.ofFn (fun i : Fin 128 => (8 + i.val) % 128)),
      .dense (Array.ofFn (fun i : Fin 120 => 8 + i.val))]).get? n = some (n % 128)
    change n < 16384 at hn
    by_cases h0 : n < 8
    · simp [Column.get?, getFromBlocks, Block.length, dense_range_get, h0]
      omega
    · by_cases h1 : n - 8 < 16256
      · simp [Column.get?, getFromBlocks, Block.length, periodic_cyclic_get, h0, h1]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, h1,
          dense_affine_get]
        omega
  · change (Column.mk #[.dense (Array.range 8),
      .periodic 511 0 (Array.ofFn (fun i : Fin 512 => (8 + i.val) % 512)),
      .affine 504 8 1]).get? n = some (n % 512)
    change n < 262144 at hn
    exact xor9_second n hn

theorem padding_get (kind : Fin 5) (j : Fin 5) (n : Nat)
    (hn : n < (xorData kind).length) :
    (xorData kind).columns[j.val + 3].get? n = some 0 := by
  have column : (xorData kind).columns[j.val + 3] =
      Column.mk #[.affine (xorData kind).length 0 0] := by
    fin_cases kind <;> fin_cases j <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

theorem tag_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[8].get? n = some (chunkTag kind) := by
  have column : (xorData kind).columns[8] =
      Column.mk #[.affine (xorData kind).length (chunkTag kind) 0] := by
    fin_cases kind <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

private theorem output_checks (kind : Fin 5) :
    checkBlocks (fun n => n / chunkSize kind ^^^ n % chunkSize kind) 0
      (xorData kind).columns[2].blocks.toList = true := by
  exact imported_xor_output_checks kind

private theorem literal_size {α : Type*} (values : List α) :
    (Array.mk values).size = values.length := rfl

private theorem output_covered (kind : Fin 5) :
    (((xorData kind).columns[2]'(by decide)).blocks.toList.map Block.length).sum =
      (xorData kind).length := by
  fin_cases kind
  all_goals dsimp only [xorData, xor8Data, xor3Data, xor4Data, xor7Data, xor9Data,
    Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[2].get? n = some (n / chunkSize kind ^^^ n % chunkSize kind) := by
  have covered := output_covered kind
  have h := checkBlocks_sound _ _ 0 n (output_checks kind) (by simpa only [covered] using hn)
  simpa only [Column.get?, Nat.zero_add] using h

end Airbender.Blake2G.Proofs.XorColumns
