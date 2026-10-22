import Human.Theorems
import Slop.RV.FsCheck.Inj

/-! `RV.NonVacuousOf`: for any image that fits in ROM, a start state (the image at address 0, zero elsewhere) and
inputs with a right claim and path (zero input, empty path to the input's own digest, the claim's limbs from
`ofLimbs_surj`) and with a wrong one (the same, with a root that differs in its first word). -/

namespace RV
open Spec

/-- Some claim is right for any input. -/
theorem exists_claim (w : Vector Word 5) : ∃ v0 v1 v2 v3 : Word, claimOK w #v[v0, v1, v2, v3] := by
  obtain ⟨l0, l1, l2, l3, h⟩ := ofLimbs_surj (poly4 (challenge (blake5 w)))
  have hw : ∀ l : F, ((BitVec.ofNat 32 l.val).toNat : F) = l := fun l => by
    have : l.val < 2 ^ 32 := lt_trans (ZMod.val_lt l) (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this, ZMod.natCast_zmod_val]
  exact ⟨BitVec.ofNat 32 l0.val, BitVec.ofNat 32 l1.val, BitVec.ofNat 32 l2.val, BitVec.ofNat 32 l3.val, by
    simp only [claimOK, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, hw, h]⟩

/-- The input's own digest is the root of the empty path. -/
theorem pathOK_nil (w : Vector Word 5) : pathOK w (blake5 w) [] := rfl

/-- A root that differs from the digest in its first word is wrong for the empty path. -/
theorem not_pathOK_nil (w : Vector Word 5) : ¬ pathOK w ((blake5 w).set 0 ((blake5 w)[0] + 1)) [] := by
  intro h
  have := congrArg (·[0]) h
  simp only [merkleRoot, List.foldl_nil, Vector.getElem_set_self] at this
  exact absurd this (by bv_omega)

/-- The image at address 0, zero elsewhere; input `inp`. -/
def imageState (bytes : Array (BitVec 8)) (inp : List Word) : State :=
  { pc := 0, regFile := fun _ => 0, mem := fun a => if h : a.toNat < bytes.size then bytes[a.toNat] else 0,
    input := inp }

theorem imageState_assumptions (bytes : Array (BitVec 8)) (hrom : bytes.size ≤ ROM_END) (x y0 y1 y2 y3 v0 v1 v2 v3 : Word)
    (root : Vector Word 8) (hx : x.toNat ≤ P) (hy0 : y0.toNat < BabyBearP) (hy1 : y1.toNat < BabyBearP)
    (hy2 : y2.toNat < BabyBearP) (hy3 : y3.toNat < BabyBearP) :
    Assumptions bytes (imageState bytes (x :: y0 :: y1 :: y2 :: y3 :: v0 :: v1 :: v2 :: v3 :: pathInput root []))
      x y0 y1 y2 y3 v0 v1 v2 v3 root [] [] := by
  simp only [ROM_END] at hrom
  refine ⟨rfl, fun i hi => ?_, fun a h1 _ => ?_, by simp [imageState], by simp, hx, hy0, hy1, hy2, hy3⟩
  · have : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    simp only [imageState, this, hi, dite_true]
  · simp only [ROM_END] at h1
    simp only [imageState, show ¬ a.toNat < bytes.size by omega, dite_false]

/-- The final theorem's assumptions can be met, with a right and with a wrong claim and path. -/
theorem nonvacuous_of (bytes : Array (BitVec 8)) (hrom : bytes.size ≤ ROM_END) : NonVacuousOf bytes := by
  have hP : (0 : Word).toNat ≤ P := by decide
  have hB : (0 : Word).toNat < BabyBearP := by decide
  obtain ⟨v0, v1, v2, v3, hv⟩ := exists_claim #v[0, 0, 0, 0, 0]
  exact ⟨⟨_, 0, 0, 0, 0, 0, v0, v1, v2, v3, _, [], [],
      imageState_assumptions bytes hrom 0 0 0 0 0 v0 v1 v2 v3 _ hP hB hB hB hB, hv, pathOK_nil _⟩,
    ⟨_, 0, 0, 0, 0, 0, v0, v1, v2, v3, _, [], [],
      imageState_assumptions bytes hrom 0 0 0 0 0 v0 v1 v2 v3 _ hP hB hB hB hB, fun h => not_pathOK_nil _ h.2⟩⟩

end RV
