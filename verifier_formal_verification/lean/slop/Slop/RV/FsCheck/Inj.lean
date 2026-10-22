import Human.SpecExt4
import Mathlib.Tactic.ComputeDegree

/-! Every `E4` element has limbs, and they are unique: `{1, w, w², w³}` is a basis of `F[w]/(w⁴ - 11)`. -/

namespace Spec
open Polynomial

instance : Fact (1 < RV.BabyBearP) := ⟨by decide⟩

theorem ofLimbs_eq_mk (l0 l1 l2 l3 : F) :
    ofLimbs l0 l1 l2 l3 = AdjoinRoot.mk (X ^ 4 - C 11 : F[X]) (C l0 + C l1 * X ^ 2 + C l2 * X + C l3 * X ^ 3) := by
  simp [ofLimbs, w, AdjoinRoot.mk_C, map_add, map_mul, map_pow, AdjoinRoot.mk_X]

theorem ofLimbs_inj {a0 a1 a2 a3 b0 b1 b2 b3 : F} (h : ofLimbs a0 a1 a2 a3 = ofLimbs b0 b1 b2 b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  rw [ofLimbs_eq_mk, ofLimbs_eq_mk, AdjoinRoot.mk_eq_mk] at h
  set d : F[X] := C a0 + C a1 * X ^ 2 + C a2 * X + C a3 * X ^ 3 - (C b0 + C b1 * X ^ 2 + C b2 * X + C b3 * X ^ 3)
  have hdeg : d.degree < (X ^ 4 - C 11 : F[X]).degree := by
    rw [degree_X_pow_sub_C (by norm_num)]
    have : d.natDegree ≤ 3 := by simp only [d]; compute_degree!
    exact lt_of_le_of_lt (degree_le_of_natDegree_le this) (by norm_num)
  have hm : (X ^ 4 - C 11 : F[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hd : d = 0 := by
    rw [← (modByMonic_eq_zero_iff_dvd hm).mpr h, (modByMonic_eq_self_iff hm).mpr hdeg]
  have c0 := congrArg (·.coeff 0) hd
  have c1 := congrArg (·.coeff 2) hd
  have c2 := congrArg (·.coeff 1) hd
  have c3 := congrArg (·.coeff 3) hd
  simp [d, coeff_X_pow, coeff_X, coeff_C] at c0 c1 c2 c3
  exact ⟨sub_eq_zero.mp c0, sub_eq_zero.mp c1, sub_eq_zero.mp c2, sub_eq_zero.mp c3⟩

theorem ofLimbs_surj (e : E4) : ∃ l0 l1 l2 l3 : F, ofLimbs l0 l1 l2 l3 = e := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective e
  have hm : (X ^ 4 - C 11 : F[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  set q := p %ₘ (X ^ 4 - C 11 : F[X]) with hqd
  have hq : AdjoinRoot.mk (X ^ 4 - C 11 : F[X]) q = AdjoinRoot.mk _ p := by
    rw [AdjoinRoot.mk_eq_mk, hqd, modByMonic_eq_sub_mul_div p]
    exact ⟨-(p /ₘ (X ^ 4 - C 11)), by ring⟩
  have hdeg : q.natDegree < 4 := by
    have := natDegree_modByMonic_lt p hm (by
      intro h; have := congrArg natDegree h; rw [natDegree_X_pow_sub_C] at this; simp at this)
    rwa [natDegree_X_pow_sub_C] at this
  refine ⟨q.coeff 0, q.coeff 2, q.coeff 1, q.coeff 3, ?_⟩
  rw [ofLimbs_eq_mk, ← hq]
  congr 1
  ext n
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  rcases n with _ | _ | _ | _ | n <;> simp
  rw [coeff_eq_zero_of_natDegree_lt (by omega)]

end Spec
