import Human.Delegations
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card

/-! Airbender's Keccak special5 delegation (CSR `0x7cb`), one call at a time: the 31 lanes as seen through the slots of
round `r` (`Rep`: lane `p` in slot `laneSlot r p`, scratch lane `i` at `25 + i`), and what each of the seven
operations does to that view (`op0_rep` … `op6_rep`). -/

namespace RV.Delegation
open Spec
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem piSrc_inj : Function.Injective piSrc := by decide

theorem laneSlot_inj : ∀ r, Function.Injective (laneSlot r)
  | 0 => fun _ _ h => h
  | r + 1 => fun _ _ h => piSrc_inj (laneSlot_inj r h)

theorem laneSlot_val_eq (r : Nat) (a b : Fin 25) : ((laneSlot r a).val = (laneSlot r b).val) ↔ a = b :=
  ⟨fun h => laneSlot_inj r (Fin.ext h), fun h => h ▸ rfl⟩

theorem lane_eq_iff (x y x' y' : Fin 5) : lane x y = lane x' y' ↔ x = x' ∧ y = y' := by
  simp only [lane, Fin.ext_iff, Fin.mk.injEq]; omega

theorem slot_ne_scratch (a : Fin 25) (k : Nat) : (a.val = 25 + k) ↔ False := ⟨fun e => by omega, False.elim⟩
theorem scratch_ne_slot (a : Fin 25) (k : Nat) : (25 + k = a.val) ↔ False := ⟨fun e => by omega, False.elim⟩

theorem fin25_val_ne (a : Fin 25) {k : Nat} (h : 25 ≤ k) : (a.val = k) ↔ False := ⟨fun e => by omega, False.elim⟩

theorem slot_ne_25 (a : Fin 25) : (a.val = 25) ↔ False := ⟨fun e => by omega, False.elim⟩
theorem ne_slot_25 (a : Fin 25) : (25 = a.val) ↔ False := ⟨fun e => by omega, False.elim⟩

theorem finRange6_foldl {α} (f : α → Fin 6 → α) (a : α) :
    (List.finRange 6).foldl f a = f (f (f (f (f (f a 0) 1) 2) 3) 4) 5 := rfl

theorem laneSlot_succ (r : Nat) (p : Fin 25) : laneSlot (r + 1) p = laneSlot r (piSrc p) := rfl

theorem piSrc_lane_eq (k x k' x' : Fin 5) : piSrc (lane k x) = piSrc (lane k' x') ↔ k = k' ∧ x = x' := by
  rw [piSrc_inj.eq_iff, lane_eq_iff]

/-- `S` holds the lanes `V` in the slots of round `r` and the scratch lanes `W`. -/
def Rep (r : Nat) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31) : Prop :=
  (∀ p : Fin 25, S[(laneSlot r p).val] = V p) ∧ ∀ i : Fin 6, S[25 + i.val] = W i

theorem op0_rep (r : Nat) (hr : r ≤ 24) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) (c : Lane) (hc : c = V (lane x 0) ^^^ (if x = 0 then delayedRC r else 0)) :
    Rep r (Function.update V (lane x 0) c)
      (Function.update W x.castSucc (c ^^^ V (lane x 1) ^^^ V (lane x 2) ^^^ V (lane x 3) ^^^ V (lane x 4)))
      (special5Step 0 x r S) := by
  subst hc
  obtain ⟨hl, hs⟩ := h
  constructor
  · intro p
    simp only [special5Step, special5Slots, hr, and_self, true_or, ↓reduceIte, slot, scratch, special5Op,
      finRange6_foldl, Vector.getElem_set, Fin.getElem_fin, Fin.val_castLE, Fin.val_castSucc, laneSlot_val_eq,
      slot_ne_scratch, scratch_ne_slot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hl,
      Function.update_apply]
    clear hl hs
    split_ifs <;> subst_vars <;> simp_all [lane_eq_iff]
  · intro i
    simp only [special5Step, special5Slots, hr, and_self, true_or, ↓reduceIte, slot, scratch, special5Op,
      finRange6_foldl, Vector.getElem_set, Fin.getElem_fin, Fin.val_castLE, Fin.val_castSucc, laneSlot_val_eq,
      slot_ne_scratch, scratch_ne_slot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hl, hs,
      Function.update_apply, Nat.add_left_cancel_iff]
    by_cases hx : x.val = i.val
    · rw [if_pos hx, if_pos (show i = x.castSucc from Fin.ext (by rw [Fin.val_castSucc]; exact hx.symm))]
    · rw [if_neg hx, if_neg (show ¬i = x.castSucc from fun e => hx (by rw [e, Fin.val_castSucc]))]


theorem Rep.scratch' {r V W S} (h : Rep r V W S) :
    S[25] = W 0 ∧ S[26] = W 1 ∧ S[27] = W 2 ∧ S[28] = W 3 ∧ S[29] = W 4 ∧ S[30] = W 5 :=
  ⟨h.2 0, h.2 1, h.2 2, h.2 3, h.2 4, h.2 5⟩

/-- The simp set reading a Keccak call's writes back. -/
macro "kread" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp only [$ts,*, special5Step, special5Slots, and_self, true_or, or_true, ↓reduceIte,
  slot, scratch, special5Op, finRange6_foldl, Vector.getElem_set, Fin.getElem_fin, Fin.val_castLE, Fin.val_castSucc,
  laneSlot_val_eq, laneSlot_succ, slot_ne_scratch, scratch_ne_slot, Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.cons_val, Function.update_apply, Nat.add_left_cancel_iff, Fin.isValue, and_true, true_and, Nat.lt_irrefl, false_and, false_or,
  Nat.one_ne_zero, Nat.lt_add_one, Nat.zero_lt_succ, Nat.reduceLT, Fin.val_zero, Nat.add_zero, slot_ne_25, ne_slot_25, fin25_val_ne])

theorem op1_rep (r : Nat) (hr : r < 24) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    Rep r V ![W 0 ^^^ (W 2).rotateLeft 1, W 1, W 2 ^^^ (W 4).rotateLeft 1, W 3, W 4, (W 0).rotateLeft 1]
      (special5Step 1 0 r S) := by
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := h.scratch'
  obtain ⟨hl, hs⟩ := h
  constructor
  · intro p; kread [hr, hl]
  · intro i; fin_cases i <;> simp [special5Step, special5Slots, special5Op, finRange6_foldl, scratch, hr, w0, w1, w2, w3, w4, w5,
      Vector.getElem_set]

theorem op2_rep (r : Nat) (hr : r < 24) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    Rep r V ![W 0, W 1 ^^^ (W 3).rotateLeft 1, W 2, W 3 ^^^ W 5, W 4 ^^^ (W 1).rotateLeft 1, W 5]
      (special5Step 2 0 r S) := by
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := h.scratch'
  obtain ⟨hl, hs⟩ := h
  constructor
  · intro p; kread [hr, hl]
  · intro i; fin_cases i <;> simp [special5Step, special5Slots, special5Op, finRange6_foldl, scratch, hr, w0, w1, w2,
      w3, w4, w5, Vector.getElem_set]

/-- Column `x` set to `g`. -/
def setCol (V : Fin 25 → Lane) (x : Fin 5) (g : Fin 5 → Lane) : Fin 25 → Lane :=
  Function.update (Function.update (Function.update (Function.update (Function.update V (lane x 0) (g 0))
    (lane x 1) (g 1)) (lane x 2) (g 2)) (lane x 3) (g 3)) (lane x 4) (g 4)

theorem op3_rep (r : Nat) (hr : r < 24) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    Rep r (setCol V x fun y => V (lane x y) ^^^ W (x - 1).castSucc) W (special5Step 3 x r S) := by
  obtain ⟨hl, hs⟩ := h
  have hsx : S[25 + (x - 1).val] = W (x - 1).castSucc := hs (x - 1).castSucc
  constructor
  · intro p; kread [hr, hl, hsx, setCol]
    clear hl hs hsx
    split_ifs <;> subst_vars <;> simp_all [lane_eq_iff]
  · intro i; kread [hr, hl, hsx, setCol]
    by_cases hh : (x - 1).val = i.val
    · rw [if_pos hh]; congr 1; exact Fin.ext (by rw [Fin.val_castSucc]; exact hh)
    · rw [if_neg hh]; exact hs i

theorem op4_rep (r : Nat) (hr : r < 24) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    Rep r (setCol V x fun y => (V (lane x y)).rotateLeft (rhoOffset x y)) W (special5Step 4 x r S) := by
  obtain ⟨hl, hs⟩ := h
  have hs0 : S[25] = W 0 := hs 0
  constructor
  · intro p; kread [hr, hl, setCol]
    clear hl hs hs0
    split_ifs <;> subst_vars <;> simp_all [lane_eq_iff]
  · intro i; kread [hr, hl, hs0, setCol]
    by_cases hh : 25 = 25 + i.val
    · rw [if_pos hh]; congr 1; exact Fin.ext (by simp; omega)
    · rw [if_neg hh]; exact hs i

theorem op5_rep (r : Nat) (hr : r < 24) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    let A := fun k => V (piSrc (lane k x))
    Rep r (Function.update (Function.update V (piSrc (lane 1 x)) (A 1 ^^^ (~~~A 2 &&& A 3)))
        (piSrc (lane 2 x)) (A 2 ^^^ (~~~A 3 &&& A 4)))
      (Function.update (Function.update W 0 (~~~A 1 &&& A 2)) 1 (A 1)) (special5Step 5 x r S) := by
  intro A
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := h.scratch'
  obtain ⟨hl, hs⟩ := h
  constructor
  · intro p; kread [hr, hl]
    clear hl hs w0 w1 w2 w3 w4 w5
    split_ifs <;> subst_vars <;> simp_all [A, piSrc_lane_eq]
  · intro i; fin_cases i <;> simp [special5Step, special5Slots, special5Op, finRange6_foldl, scratch, slot, hr, w0,
      w1, w2, w3, w4, w5, Vector.getElem_set, laneSlot_succ, hl, A, Function.update_apply, fin25_val_ne]

theorem op6_rep (r : Nat) (hr : r < 24) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    let A := fun k => V (piSrc (lane k x))
    Rep r (Function.update (Function.update (Function.update V (piSrc (lane 0 x)) (A 0 ^^^ W 0))
        (piSrc (lane 3 x)) (A 3 ^^^ (~~~A 4 &&& A 0))) (piSrc (lane 4 x)) (A 4 ^^^ (~~~A 0 &&& W 1)))
      W (special5Step 6 x r S) := by
  intro A
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := h.scratch'
  obtain ⟨hl, hs⟩ := h
  constructor
  · intro p; kread [hr, hl, w0, w1]
    clear hl hs w2 w3 w4 w5
    split_ifs <;> subst_vars <;> simp_all [A, piSrc_lane_eq]
  · intro i; fin_cases i <;> simp [special5Step, special5Slots, special5Op, finRange6_foldl, scratch, slot, hr, w0,
      w1, w2, w3, w4, w5, Vector.getElem_set, laneSlot_succ, hl, A, Function.update_apply, fin25_val_ne]

end RV.Delegation
