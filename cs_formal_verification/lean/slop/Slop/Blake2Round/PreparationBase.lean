import Slop.Blake2Round.ArtifactChecks
import Slop.Blake2Round.OpIndex
import Slop.Blake2G.OpIndex
import Human.Circuits.Blake2Round.Preparation
import Slop.Constraints
import Slop.Arithmetic.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2Round.Preparation.Proofs
open Arithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem iv_limbs : iv = #v[
    ⟨58983, 27145⟩, ⟨44677, 47975⟩, ⟨62322, 15470⟩, ⟨62778, 42319⟩,
    ⟨21119, 20750⟩, ⟨26764, 39685⟩, ⟨55723, 8067⟩, ⟨52505, 23520⟩] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> norm_num [iv, configuredIV, compressionIV, Specs.BLAKE3.iv, splitWord, limbBase]
  all_goals decide

theorem configured_limbs : configuredIV = #v[
    ⟨58951, 27400⟩, ⟨44677, 47975⟩, ⟨62322, 15470⟩, ⟨62778, 42319⟩,
    ⟨21119, 20750⟩, ⟨26764, 39685⟩, ⟨55723, 8067⟩, ⟨52505, 23520⟩] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> norm_num [iv, configuredIV, compressionIV, Specs.BLAKE3.iv, splitWord, limbBase]
  all_goals decide

theorem compression_limbs : compressionIV = #v[
    ⟨58983, 27145⟩, ⟨44677, 47975⟩, ⟨62322, 15470⟩, ⟨62778, 42319⟩,
    ⟨21055, 20750⟩, ⟨26764, 39685⟩, ⟨9812, 57468⟩, ⟨52505, 23520⟩] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> norm_num [iv, configuredIV, compressionIV, Specs.BLAKE3.iv, splitWord, limbBase]
  all_goals decide

theorem get_append8 (xs ys : Vector Word 8) (i : Nat) (hi : i < 16) :
    (show Vector Word 16 from xs ++ ys)[i] = if h : i < 8 then xs[i] else ys[i - 8] := by
  exact Vector.getElem_append (xs := xs) (ys := ys) hi
theorem get_path_left (xs : Vector Word 16) (ys : Vector Word 8) (i : Nat) (hi : i < 16) :
    (show Vector Word 16 from xs.take 8 ++ ys)[i] = if h : i < 8 then xs[i] else ys[i - 8] := by
  have e : (show Vector Word 16 from xs.take 8 ++ ys)[i] =
      if h : i < 8 then (xs.take 8)[i] else ys[i - 8] :=
    Vector.getElem_append (xs := xs.take 8) (ys := ys) hi
  rw [e]
  split
  · exact Vector.getElem_take (xs := xs) (j := 8) (by omega)
  · rfl
theorem get_path_right (xs : Vector Word 8) (ys : Vector Word 16) (i : Nat) (hi : i < 16) :
    (show Vector Word 16 from xs ++ ys.take 8)[i] = if h : i < 8 then xs[i] else ys[i - 8] := by
  have e : (show Vector Word 16 from xs ++ ys.take 8)[i] =
      if h : i < 8 then xs[i] else (ys.take 8)[i - 8] :=
    Vector.getElem_append (xs := xs) (ys := ys.take 8) hi
  rw [e]
  split
  · rfl
  · exact Vector.getElem_take (xs := ys) (j := 8) (by omega)

theorem words_eq {p n : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {columns : Vector (Nat × Nat) n} {expected : Vector Word n}
    (bounds : ∀ i : Fin n, expected[i].lo < p ∧ expected[i].hi < p)
    (equalities : ∀ i : Fin n, w columns[i].1 = (expected[i].lo : ZMod p) ∧
      w columns[i].2 = (expected[i].hi : ZMod p)) : words w columns = expected := by
  apply Vector.ext
  intro i hi
  obtain ⟨lo, high⟩ := equalities ⟨i, hi⟩
  obtain ⟨loBound, hiBound⟩ := bounds ⟨i, hi⟩
  simp only [Fin.getElem_fin] at lo high loBound hiBound
  simp only [words, Vector.getElem_map]
  rw [lo, high, ZMod.val_natCast_of_lt loBound, ZMod.val_natCast_of_lt hiBound]

theorem read_bounds {p n : Nat} [Fact p.Prime] (w : Nat → ZMod p)
    (columns : Vector (Nat × Nat) n) (i : Fin n) :
    (words w columns)[i].lo < p ∧ (words w columns)[i].hi < p := by
  simp only [words, Fin.getElem_fin, Vector.getElem_map]
  exact ⟨ZMod.val_lt _, ZMod.val_lt _⟩


/-- The expected output words of `extended`, for the chosen first-round and compression flags. -/
abbrev extendedExpected {p : Nat} (first compression : Bool) (w : Nat → ZMod p) : Vector Word 16 :=
  if first then words w Variables.chainingInputs ++
      (if compression then compressionIV
        else (iv.set 4 (words w Variables.extendedReads)[12]).set 6
          (words w Variables.extendedReads)[14])
      else words w Variables.extendedReads

/-- The constraint indices of the `extended` high/low limb equations (for the range proofs). -/
abbrev loIdx : Vector Nat 16 := #v[5, 9, 13, 17, 21, 25, 29, 33, 36, 38, 40, 42, 48, 44, 50, 46]
abbrev hiIdx : Vector Nat 16 := #v[7, 11, 15, 19, 23, 27, 31, 35, 37, 39, 41, 43, 49, 45, 51, 47]

theorem loIdx_lt : ∀ j : Fin 16, loIdx[j] < 352 := by decide
theorem hiIdx_lt : ∀ j : Fin 16, hiIdx[j] < 352 := by decide

end Airbender.Blake2Round.Preparation.Proofs
