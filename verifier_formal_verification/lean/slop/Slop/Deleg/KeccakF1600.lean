import Slop.Deleg.KeccakRound

/-! The Keccak-f1600 delegations (CSRs `0x7cd` column parity, `0x7cc` θ+ρ, `0x7ce` χ) on the slot view: one call
of each (`par_rep`, `thetaRho_rep`, `chi_rep`), and a round of 15 calls is a Keccak-f round (`f1600_round`). -/

namespace RV.Delegation
open Spec
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem finRange5_foldl {α} (f : α → Fin 5 → α) (a : α) :
    (List.finRange 5).foldl f a = f (f (f (f (f a 0) 1) 2) 3) 4 := rfl

macro "fread" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp only [$ts,*, f1600Step,
  columnParity, set5, finRange5_foldl, ↓reduceIte, slot, scratch, Vector.getElem_set, Fin.getElem_fin,
  Fin.val_castLE, Fin.val_castSucc, laneSlot_val_eq, laneSlot_succ, slot_ne_scratch, scratch_ne_slot,
  Function.update_apply, Nat.add_left_cancel_iff, Fin.isValue, Fin.val_zero, Nat.add_zero, slot_ne_25, ne_slot_25,
  fin25_val_ne])

/-- Column parity: the same as special5's op 0. -/
theorem par_rep (r : Nat) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) (c : Lane) (hc : c = V (lane x 0) ^^^ (if x = 0 then delayedRC r else 0)) :
    Rep r (Function.update V (lane x 0) c)
      (Function.update W x.castSucc (c ^^^ V (lane x 1) ^^^ V (lane x 2) ^^^ V (lane x 3) ^^^ V (lane x 4)))
      (f1600Step 0 x r S) := by
  subst hc
  obtain ⟨hl, hs⟩ := h
  by_cases hx : x = 0
  · subst hx
    constructor
    · intro p; fread [hl]
      clear hl hs
      split_ifs <;> subst_vars <;> simp_all [lane_eq_iff]
    · intro i; fread [hl, hs, lane_eq_iff]
      by_cases hi : i.val = 0
      · rw [if_pos (by omega), if_pos (show i = Fin.castSucc 0 from Fin.ext hi)]; simp
      · rw [if_neg (by omega), if_neg (show ¬i = Fin.castSucc 0 from fun e => hi (by rw [e]; rfl))]
  · constructor
    · intro p; fread [hl, hx, BitVec.xor_zero]
      split_ifs with h <;> simp [h]
    · intro i; fread [hl, hs, hx, BitVec.xor_zero]
      by_cases hh : x.val = i.val
      · rw [if_pos hh, if_pos (show i = x.castSucc from Fin.ext (by rw [Fin.val_castSucc]; exact hh.symm))]; simp
      · rw [if_neg hh, if_neg (show ¬i = x.castSucc from fun e => hh (by rw [e, Fin.val_castSucc]))]

theorem thetaRho_rep (r : Nat) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    Rep r (setCol V x fun y => (V (lane x y) ^^^ thetaD (fun i => W i.castSucc) x).rotateLeft (rhoOffset x y)) W
      (f1600Step 3 x r S) := by
  obtain ⟨hl, hs⟩ := h
  have hs' : ∀ i : Fin 5, S[25 + i.val] = W i.castSucc := fun i => hs i.castSucc
  constructor
  · intro p; fread [hl, hs', setCol]
    clear hl hs hs'
    split_ifs <;> subst_vars <;> simp_all [lane_eq_iff]
  · intro i; fread [hl, hs, hs']

theorem chi_rep (r : Nat) (x : Fin 5) (V : Fin 25 → Lane) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r V W S) :
    let A := fun k => V (piSrc (lane k x))
    Rep r (Function.update (Function.update (Function.update (Function.update (Function.update V
        (piSrc (lane 0 x)) (A 0 ^^^ (~~~A 1 &&& A 2))) (piSrc (lane 1 x)) (A 1 ^^^ (~~~A 2 &&& A 3)))
        (piSrc (lane 2 x)) (A 2 ^^^ (~~~A 3 &&& A 4))) (piSrc (lane 3 x)) (A 3 ^^^ (~~~A 4 &&& A 0)))
        (piSrc (lane 4 x)) (A 4 ^^^ (~~~A 0 &&& A 1)))
      W (f1600Step 5 x r S) := by
  intro A
  obtain ⟨hl, hs⟩ := h
  constructor
  · intro p; fread [hl, Fin.reduceAdd]
    clear hl hs
    split_ifs <;> subst_vars <;> simp_all [A, piSrc_lane_eq]
  · intro i; fread [hl, hs]

def fsteps (r : Nat) (l : List (Nat × Fin 5)) (S : Vector Lane 31) : Vector Lane 31 :=
  l.foldl (fun S c => f1600Step c.1 c.2 r S) S

theorem fsteps_append (r : Nat) (l l' : List (Nat × Fin 5)) (S : Vector Lane 31) :
    fsteps r (l ++ l') S = fsteps r l' (fsteps r l S) := List.foldl_append ..

/-- The 15 calls of a round, as (op, x). -/
def fRoundCalls : List (Nat × Fin 5) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] ++ [(3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] ++
    [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4)]

theorem fstageP (r : Nat) (B : Vector Lane 25) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => B[p]) W S) :
    let A := iota' r B
    Rep r (fun p => A[p]) ![parity A 0, parity A 1, parity A 2, parity A 3, parity A 4, W 5]
      (fsteps r [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] S) := by
  intro A
  simp only [fsteps, List.foldl_cons, List.foldl_nil]
  have h1 := par_rep r 0 _ _ _ h _ rfl
  have h2 := par_rep r 1 _ _ _ h1 _ rfl
  have h3 := par_rep r 2 _ _ _ h2 _ rfl
  have h4 := par_rep r 3 _ _ _ h3 _ rfl
  have h5 := par_rep r 4 _ _ _ h4 _ rfl
  refine h5.congr ?_ ?_
  · funext p; fin_cases p <;> simp [Function.update_apply, A, iota', lane, Vector.getElem_set]
  · funext i; fin_cases i <;> simp [Function.update_apply, A, iota', lane, parity, Vector.getElem_set]

theorem fstageT (r : Nat) (A : Vector Lane 25) (w : Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => A[p]) ![parity A 0, parity A 1, parity A 2, parity A 3, parity A 4, w] S) :
    Rep r (fun p => (rho (theta A))[p]) ![parity A 0, parity A 1, parity A 2, parity A 3, parity A 4, w]
      (fsteps r [(3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] S) := by
  simp only [fsteps, List.foldl_cons, List.foldl_nil]
  have h1 := thetaRho_rep r 0 _ _ _ h
  have h2 := thetaRho_rep r 1 _ _ _ h1
  have h3 := thetaRho_rep r 2 _ _ _ h2
  have h4 := thetaRho_rep r 3 _ _ _ h3
  have h5 := thetaRho_rep r 4 _ _ _ h4
  refine h5.congr ?_ rfl
  funext p; fin_cases p <;> simp [Function.update_apply, setCol, rho, theta, thetaD, lane, laneX, laneY,
    Vector.getElem_ofFn]

theorem fstageX (r : Nat) (A : Vector Lane 25) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => A[p]) W S) :
    Rep (r + 1) (fun p => (chi (pi A))[p]) W (fsteps r [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4)] S) := by
  simp only [fsteps, List.foldl_cons, List.foldl_nil]
  have h1 := chi_rep r 0 _ _ _ h
  have h2 := chi_rep r 1 _ _ _ h1
  have h3 := chi_rep r 2 _ _ _ h2
  have h4 := chi_rep r 3 _ _ _ h3
  have h5 := chi_rep r 4 _ _ _ h4
  refine ⟨fun p => ?_, h5.2⟩
  simp only [laneSlot_succ]
  refine (h5.1 (piSrc p)).trans ?_
  fin_cases p <;> simp [Function.update_apply, chi, pi, piSrc, lane, laneX, laneY, Vector.getElem_ofFn]

/-- Round `r`'s 15 calls take the lanes (before the delayed ι) to the next round's, in the next round's slots. -/
theorem f1600_round (r : Nat) (B : Vector Lane 25) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => B[p]) W S) :
    ∃ W', Rep (r + 1) (fun p => (chi (pi (rho (theta (iota' r B)))))[p]) W' (fsteps r fRoundCalls S) := by
  simp only [fRoundCalls, fsteps_append]
  exact ⟨_, fstageX r _ _ _ (fstageT r _ _ _ (fstageP r B W S h))⟩

end RV.Delegation
