import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Proofs.Blake2G.XorCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2G

/- Mathematical reference only; actual table definitions import their data. -/
def xorRow (width tag index : Nat) : Vector Nat 9 :=
  let a := index / 2 ^ width
  let b := index % 2 ^ width
  #v[a, b, a ^^^ b, 0, 0, 0, 0, 0, tag]

def referenceSetupRow (control : Fin 512 → Vector Nat 7) (index : Fin 344896) : Vector Nat 9 :=
  let n := index.val
  if n < 65536 then xorRow 8 4 n
  else if n < 65600 then xorRow 3 17 (n - 65536)
  else if n < 65856 then xorRow 4 18 (n - 65600)
  else if n < 82240 then xorRow 7 19 (n - 65856)
  else if h : n < 344384 then xorRow 9 20 (n - 82240)
  else
    let outputs := control ⟨n - 344384, by have bound := index.isLt; dsimp [n] at *; omega⟩
    #v[n - 344384, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4],
      outputs[5], outputs[6], 28]

namespace Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private def chunkSize (kind : Fin 5) : Nat := 2 ^ (#v[8, 3, 4, 7, 9][kind])
private def chunkTag (kind : Fin 5) : Nat := #v[4, 17, 18, 19, 20][kind]

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

private theorem first_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[0].get? n = some (n / chunkSize kind) := by
  have columns : (xorData kind).columns[0] = Column.mk #[
      .periodic (chunkSize kind) 1 (Array.replicate (chunkSize kind) 0)] := by
    fin_cases kind <;> rfl
  rw [columns]
  have positive : 0 < chunkSize kind := by fin_cases kind <;> decide
  simpa only [Column.get?, Array.toList, getFromBlocks, Block.length,
    Array.size_replicate, if_pos (native_length kind ▸ hn)] using
    periodic_constant_get _ _ n positive (native_length kind ▸ hn)

private theorem second_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[1].get? n = some (n % chunkSize kind) := by
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
    by_cases h0 : n < 8
    · simp [Column.get?, getFromBlocks, Block.length, dense_range_get, h0]
      omega
    · by_cases h1 : n - 8 < 261632
      · simp [Column.get?, getFromBlocks, Block.length, periodic_cyclic_get, h0, h1]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, h1,
          affine_get]
        omega

private theorem padding_get (kind : Fin 5) (j : Fin 5) (n : Nat)
    (hn : n < (xorData kind).length) :
    (xorData kind).columns[j.val + 3].get? n = some 0 := by
  have column : (xorData kind).columns[j.val + 3] =
      Column.mk #[.affine (xorData kind).length 0 0] := by
    fin_cases kind <;> fin_cases j <;> rfl
  rw [column]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

private theorem tag_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
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
  all_goals simp only [raw_toList_append, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Block.length,
    Array.size_ofFn, raw_size_append, literal_size, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul]

private theorem output_get (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[2].get? n = some (n / chunkSize kind ^^^ n % chunkSize kind) := by
  have covered := output_covered kind
  have h := checkBlocks_sound _ _ 0 n (output_checks kind) (by simpa only [covered] using hn)
  simpa only [Column.get?, Nat.zero_add] using h

/-- All five actual native regions have the exact bounded XOR row, including
    every physical padding and discriminator column. -/
theorem xor_region_reference (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    xorRegionRow kind n = xorRow (#v[8, 3, 4, 7, 9][kind]) (#v[4, 17, 18, 19, 20][kind]) n := by
  apply Vector.ext
  intro j hj
  have first := first_get kind n hn
  have second := second_get kind n hn
  have output := output_get kind n hn
  have tag := tag_get kind n hn
  interval_cases j
  all_goals simp only [xorRegionRow, Vector.getElem_map, xorRow, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · simp only [chunkSize, first, Option.getD_some]
  · simp only [chunkSize, second, Option.getD_some]
  · simp only [chunkSize, output, Option.getD_some]
  · have zero : (xorData kind).columns[3].get? n = some 0 := padding_get kind 0 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[4].get? n = some 0 := padding_get kind 1 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[5].get? n = some 0 := padding_get kind 2 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[6].get? n = some 0 := padding_get kind 3 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[7].get? n = some 0 := padding_get kind 4 n hn
    simp only [zero, Option.getD_some]
  · simp only [tag, Option.getD_some, chunkTag]

/-- Native imported fixed rows recover the former mathematical characterization;
    the supplied controller remains arbitrary. -/
theorem setup_row_characterization (control : Fin 512 → Vector Nat 7) (index : Fin 344896) :
    setupRow control index = referenceSetupRow control index := by
  have bound := index.isLt
  unfold setupRow referenceSetupRow
  dsimp only [xor8DataRegion, xor3DataRegion, xor4DataRegion, xor7DataRegion,
    xor9DataRegion, controllerDataRegion]
  split_ifs
  all_goals first
    | exact xor_region_reference _ _ (by change _ < 65536; omega)
    | exact xor_region_reference _ _ (by change _ < 64; omega)
    | exact xor_region_reference _ _ (by change _ < 256; omega)
    | exact xor_region_reference _ _ (by change _ < 16384; omega)
    | exact xor_region_reference _ _ (by change _ < 262144; omega)
    | rfl

/-- Raw imported canonical values and their signed circuit-style lift denote
    the same rows in the native field. Generic-field XOR proofs are unchanged. -/
theorem xor_region_native_cast (kind : Fin 5) (index : Fin (xorData kind).length) :
    (xorRegionRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((xorData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus)) := by
  have offset : (xorData kind).offset = 0 := by fin_cases kind <;> rfl
  apply Vector.ext
  intro j hj
  simp [xorRegionRow, TableData.row, offset, signedValue_cast]

end Proofs
end Airbender.Blake2G
