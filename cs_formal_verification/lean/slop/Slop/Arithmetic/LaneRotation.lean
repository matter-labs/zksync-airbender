module
public import Slop.Arithmetic.ByteAssembly
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.Arithmetic
set_option warningAsError true

def packLane (limbs : Vector Nat 4) : Nat :=
  limbs[0] + 65536 * (limbs[1] + 65536 * (limbs[2] + 65536 * limbs[3]))

def rotationSource (left : Fin 64) (limb : Fin 4) : Fin 4 :=
  ⟨(limb.val + 4 - left.val / 16) % 4, by omega⟩

def rotationPrevious (limb : Fin 4) : Fin 4 := ⟨(limb.val + 3) % 4, by omega⟩

def rotatedLaneLimb (limbs : Vector Nat 4) (left : Fin 64) (limb : Fin 4) : Nat :=
  let source := rotationSource left limb
  (limbs[source] * 2 ^ (left.val % 16)) % 65536 +
    limbs[rotationPrevious source] / 2 ^ (16 - left.val % 16)

/-- `rotLeft64` of a 64-bit value as a split at bit `64 - left`. -/
theorem rotLeft64_eq_split {x : Nat} (hx : x < 2 ^ 64) (left : Fin 64) :
    rotLeft64 x left = (x % 2 ^ (64 - left.val)) * 2 ^ left.val + x / 2 ^ (64 - left.val) := by
  have hl := left.isLt
  have hsub : ((64 - left : Fin 64) % 64 : Fin 64).val = (64 - left.val) % 64 := by
    rw [Fin.mod_def, Fin.sub_def]; simp
  simp only [rotLeft64, rotRight64]
  rw [hsub]
  by_cases h0 : left.val = 0
  · rw [h0]; simp only [Nat.reduceMod, Nat.sub_zero, pow_zero, Nat.mod_one, Nat.mul_one, Nat.div_one]; omega
  · rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt (by omega : 64 - left.val < 64),
      show 64 - (64 - left.val) = left.val by omega]


/-- Shifting a 16-bit limb left by `r` and truncating keeps its low `16 - r` bits. -/
theorem shifted_limb_mod {a r : Nat} (hr : r ≤ 16) :
    (a * 2 ^ r) % 65536 = (a % 2 ^ (16 - r)) * 2 ^ r := by
  have hPD : 2 ^ (16 - r) * 2 ^ r = 65536 := by rw [← pow_add, Nat.sub_add_cancel hr]; rfl
  rw [← hPD, Nat.mul_mod_mul_right]

/-- `x = L + M * T` with `L < M`, split at `M` and re-assembled with the low part shifted up by `N`. -/
theorem split_reassemble {x L M T N : Nat} (hx : x = L + M * T) (hL : L < M) :
    (x % M) * N + x / M = L * N + T := by
  subst hx
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hL, Nat.zero_add]

/-- Low and high digit of `D * h + l` in base `D`. -/
theorem digit_mod_div {D h l : Nat} (hl : l < D) : (D * h + l) % D = l ∧ (D * h + l) / D = h := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
  · rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hl, Nat.add_zero]

theorem rotated_lane_limb_bound {limbs : Vector Nat 4}
    (bounds : ∀ i : Fin 4, limbs[i] < 65536) (left : Fin 64) (limb : Fin 4) :
    rotatedLaneLimb limbs left limb < 65536 := by
  have prior := bounds (rotationPrevious (rotationSource left limb))
  have small : left.val % 16 < 16 := Nat.mod_lt _ (by decide)
  dsimp only [rotatedLaneLimb]
  rw [shifted_limb_mod small.le]
  generalize limbs[rotationSource left limb] = a
  generalize limbs[rotationPrevious (rotationSource left limb)] = b at prior ⊢
  generalize left.val % 16 = r at small ⊢
  have hPD : 2 ^ r * 2 ^ (16 - r) = 65536 := by
    rw [← pow_add, Nat.add_sub_cancel' small.le]; rfl
  have hD : 0 < 2 ^ (16 - r) := Nat.two_pow_pos _
  generalize 2 ^ r = P at hPD ⊢
  generalize 2 ^ (16 - r) = D at hPD hD ⊢
  have high : b / D < P := (Nat.div_lt_iff_lt_mul hD).2 (by rw [hPD]; exact prior)
  have low : (a % D + 1) * P ≤ D * P := Nat.mul_le_mul_right _ (Nat.mod_lt _ hD)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm D P, hPD] at low
  omega

/-- Generic in the offset `left = 16 q + r`: limbs split at bit `16 - r` (`D = 2 ^ (16 - r)`), one case per
    limb shift `q`, each an identity modulo `2 ^ r * 2 ^ (16 - r) = 65536`. -/
theorem rotate_left_of_limbs {limbs : Vector Nat 4}
    (bounds : ∀ i : Fin 4, limbs[i] < 65536) (left : Fin 64) :
    rotLeft64 (packLane limbs) left =
      packLane ((Vector.finRange 4).map (rotatedLaneLimb limbs left)) := by
  have h0 := bounds 0; have h1 := bounds 1
  have h2 := bounds 2; have h3 := bounds 3
  change limbs[(0 : Nat)] < 65536 at h0
  change limbs[(1 : Nat)] < 65536 at h1
  change limbs[(2 : Nat)] < 65536 at h2
  change limbs[(3 : Nat)] < 65536 at h3
  obtain ⟨q, r, hq, hr, hleft⟩ : ∃ q r, q < 4 ∧ r < 16 ∧ left.val = 16 * q + r :=
    ⟨left.val / 16, left.val % 16, by omega, by omega, by omega⟩
  have hdiv : left.val / 16 = q := by omega
  have hmod : left.val % 16 = r := by omega
  rw [rotLeft64_eq_split (by unfold packLane; omega), hleft,
    show 64 - (16 * q + r) = 16 * (3 - q) + (16 - r) by omega, pow_add, pow_add, pow_mul, pow_mul]
  simp only [packLane, Vector.getElem_map, Vector.getElem_finRange, rotatedLaneLimb,
    rotationSource, rotationPrevious, Fin.getElem_fin, hdiv, hmod, shifted_limb_mod hr.le]
  have hPD : 2 ^ r * 2 ^ (16 - r) = 65536 := by
    rw [← pow_add, Nat.add_sub_cancel' hr.le]; rfl
  have hD : 0 < 2 ^ (16 - r) := Nat.two_pow_pos _
  generalize 2 ^ r = P at hPD ⊢
  generalize 2 ^ (16 - r) = D at hPD hD ⊢
  obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  all_goals
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, pow_zero, Nat.one_mul]
  all_goals
    generalize limbs[0] = a0 at h0 ⊢
    generalize limbs[1] = a1 at h1 ⊢
    generalize limbs[2] = a2 at h2 ⊢
    generalize limbs[3] = a3 at h3 ⊢
    obtain ⟨g0, l0, rfl, hl0⟩ : ∃ g l, a0 = D * g + l ∧ l < D :=
      ⟨_, _, (Nat.div_add_mod a0 D).symm, Nat.mod_lt _ hD⟩
    obtain ⟨g1, l1, rfl, hl1⟩ : ∃ g l, a1 = D * g + l ∧ l < D :=
      ⟨_, _, (Nat.div_add_mod a1 D).symm, Nat.mod_lt _ hD⟩
    obtain ⟨g2, l2, rfl, hl2⟩ : ∃ g l, a2 = D * g + l ∧ l < D :=
      ⟨_, _, (Nat.div_add_mod a2 D).symm, Nat.mod_lt _ hD⟩
    obtain ⟨g3, l3, rfl, hl3⟩ : ∃ g l, a3 = D * g + l ∧ l < D :=
      ⟨_, _, (Nat.div_add_mod a3 D).symm, Nat.mod_lt _ hD⟩
    simp only [(digit_mod_div hl0).1, (digit_mod_div hl0).2, (digit_mod_div hl1).1, (digit_mod_div hl1).2,
      (digit_mod_div hl2).1, (digit_mod_div hl2).2, (digit_mod_div hl3).1, (digit_mod_div hl3).2]
  · rw [split_reassemble (L := D * g0 + l0 + 65536 * (D * g1 + l1 + 65536 * (D * g2 + l2 + 65536 * l3)))
      (T := g3) (by ring) (by omega)]
    linear_combination (g0 + 65536 * g1 + 4294967296 * g2) * hPD
  · rw [split_reassemble (L := D * g0 + l0 + 65536 * (D * g1 + l1 + 65536 * l2))
      (T := g2 + P * (D * g3 + l3)) (by linear_combination 4294967296 * (D * g3 + l3) * hPD.symm) (by omega)]
    linear_combination (65536 * g0 + 4294967296 * g1 + g3) * hPD
  · rw [split_reassemble (L := D * g0 + l0 + 65536 * l1)
      (T := g1 + P * (D * g2 + l2 + 65536 * (D * g3 + l3)))
      (by linear_combination 65536 * (D * g2 + l2 + 65536 * (D * g3 + l3)) * hPD.symm) (by omega)]
    linear_combination (4294967296 * g0 + g2 + 65536 * g3) * hPD
  · rw [split_reassemble (L := l0)
      (T := g0 + P * (D * g1 + l1 + 65536 * (D * g2 + l2 + 65536 * (D * g3 + l3))))
      (by linear_combination (D * g1 + l1 + 65536 * (D * g2 + l2 + 65536 * (D * g3 + l3))) * hPD.symm) hl0]
    linear_combination (g1 + 65536 * g2 + 4294967296 * g3) * hPD

end Airbender.Arithmetic
