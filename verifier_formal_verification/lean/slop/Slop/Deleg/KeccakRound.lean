import Slop.Deleg.KeccakSlots

/-! One round of Keccak special5 calls (27) is one Keccak-f round on the slot view, in five stages: delayed ι and the
column parities (`stageA`), θ's `D` (`stageB`), θ (`stageC`), ρ (`stageD`), π and χ (`stageE`). -/

namespace RV.Delegation
open Spec
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

def iota' (r : Nat) (B : Vector Lane 25) : Vector Lane 25 := B.set 0 (B[0] ^^^ delayedRC r)

def steps (r : Nat) (l : List (Nat × Fin 5)) (S : Vector Lane 31) : Vector Lane 31 :=
  l.foldl (fun S c => special5Step c.1 c.2 r S) S

theorem Rep.congr {r V W S V' W'} (h : Rep r V W S) (hV : V = V') (hW : W = W') : Rep r V' W' S := hV ▸ hW ▸ h

/-- ι (delayed) and the column parities. -/
theorem stageA (r : Nat) (hr : r < 24) (B : Vector Lane 25) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => B[p]) W S) :
    let A := iota' r B
    Rep r (fun p => A[p]) ![parity A 0, parity A 1, parity A 2, parity A 3, parity A 4, W 5]
      (steps r [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] S) := by
  intro A
  simp only [steps, List.foldl_cons, List.foldl_nil]
  have h1 := op0_rep r (by omega) 0 _ _ _ h _ rfl
  have h2 := op0_rep r (by omega) 1 _ _ _ h1 _ rfl
  have h3 := op0_rep r (by omega) 2 _ _ _ h2 _ rfl
  have h4 := op0_rep r (by omega) 3 _ _ _ h3 _ rfl
  have h5 := op0_rep r (by omega) 4 _ _ _ h4 _ rfl
  refine h5.congr ?_ ?_
  · funext p; fin_cases p <;> simp [Function.update_apply, A, iota', lane, Vector.getElem_set]
  · funext i; fin_cases i <;> simp [Function.update_apply, A, iota', lane, parity, Vector.getElem_set]

/-- θ's `D` from the parities. -/
theorem stageB (r : Nat) (hr : r < 24) (V : Fin 25 → Lane) (c : Fin 5 → Lane) (w : Lane) (S : Vector Lane 31)
    (h : Rep r V ![c 0, c 1, c 2, c 3, c 4, w] S) :
    Rep r V ![thetaD c 1, thetaD c 2, thetaD c 3, thetaD c 4, thetaD c 0, (c 0).rotateLeft 1]
      (steps r [(1, 0), (2, 0)] S) := by
  simp only [steps, List.foldl_cons, List.foldl_nil]
  refine (op2_rep r hr _ _ _ (op1_rep r hr _ _ _ h)).congr rfl ?_
  funext i; fin_cases i <;> simp [thetaD]

/-- θ. -/
theorem stageC (r : Nat) (hr : r < 24) (A : Vector Lane 25) (w : Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => A[p]) ![thetaD (parity A) 1, thetaD (parity A) 2, thetaD (parity A) 3, thetaD (parity A) 4,
      thetaD (parity A) 0, w] S) :
    Rep r (fun p => (theta A)[p]) ![thetaD (parity A) 1, thetaD (parity A) 2, thetaD (parity A) 3,
      thetaD (parity A) 4, thetaD (parity A) 0, w] (steps r [(3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] S) := by
  simp only [steps, List.foldl_cons, List.foldl_nil]
  have h1 := op3_rep r hr 0 _ _ _ h
  have h2 := op3_rep r hr 1 _ _ _ h1
  have h3 := op3_rep r hr 2 _ _ _ h2
  have h4 := op3_rep r hr 3 _ _ _ h3
  have h5 := op3_rep r hr 4 _ _ _ h4
  refine h5.congr ?_ rfl
  funext p; fin_cases p <;> simp [Function.update_apply, setCol, theta, lane, laneX, Vector.getElem_ofFn]

/-- ρ. -/
theorem stageD (r : Nat) (hr : r < 24) (A : Vector Lane 25) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => A[p]) W S) :
    Rep r (fun p => (rho A)[p]) W (steps r [(4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] S) := by
  simp only [steps, List.foldl_cons, List.foldl_nil]
  have h1 := op4_rep r hr 0 _ _ _ h
  have h2 := op4_rep r hr 1 _ _ _ h1
  have h3 := op4_rep r hr 2 _ _ _ h2
  have h4 := op4_rep r hr 3 _ _ _ h3
  have h5 := op4_rep r hr 4 _ _ _ h4
  refine h5.congr ?_ rfl
  funext p; fin_cases p <;> simp [Function.update_apply, setCol, rho, lane, laneX, laneY, Vector.getElem_ofFn]

/-- π (the slots of round `r + 1`) and χ. -/
theorem stageE (r : Nat) (hr : r < 24) (A : Vector Lane 25) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => A[p]) W S) :
    ∃ W', Rep (r + 1) (fun p => (chi (pi A))[p]) W'
      (steps r [(5, 0), (6, 0), (5, 1), (6, 1), (5, 2), (6, 2), (5, 3), (6, 3), (5, 4), (6, 4)] S) := by
  simp only [steps, List.foldl_cons, List.foldl_nil]
  have h1 := op5_rep r hr 0 _ _ _ h
  have h2 := op6_rep r hr 0 _ _ _ h1
  have h3 := op5_rep r hr 1 _ _ _ h2
  have h4 := op6_rep r hr 1 _ _ _ h3
  have h5 := op5_rep r hr 2 _ _ _ h4
  have h6 := op6_rep r hr 2 _ _ _ h5
  have h7 := op5_rep r hr 3 _ _ _ h6
  have h8 := op6_rep r hr 3 _ _ _ h7
  have h9 := op5_rep r hr 4 _ _ _ h8
  have h10 := op6_rep r hr 4 _ _ _ h9
  refine ⟨_, fun p => ?_, h10.2⟩
  simp only [laneSlot_succ]
  refine (h10.1 (piSrc p)).trans ?_
  fin_cases p <;> simp [Function.update_apply, chi, pi, piSrc, lane, laneX, laneY, Vector.getElem_ofFn]

theorem steps_append (r : Nat) (l l' : List (Nat × Fin 5)) (S : Vector Lane 31) :
    steps r (l ++ l') S = steps r l' (steps r l S) := List.foldl_append ..

/-- The 27 calls of a round, as (op, x). -/
def roundCalls : List (Nat × Fin 5) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)] ++ [(1, 0), (2, 0)] ++ [(3, 0), (3, 1), (3, 2), (3, 3), (3, 4)] ++
    [(4, 0), (4, 1), (4, 2), (4, 3), (4, 4)] ++
    [(5, 0), (6, 0), (5, 1), (6, 1), (5, 2), (6, 2), (5, 3), (6, 3), (5, 4), (6, 4)]

/-- Round `r`'s calls take the lanes (before the delayed ι) to the next round's, in the next round's slots. -/
theorem round_rep (r : Nat) (hr : r < 24) (B : Vector Lane 25) (W : Fin 6 → Lane) (S : Vector Lane 31)
    (h : Rep r (fun p => B[p]) W S) :
    ∃ W', Rep (r + 1) (fun p => (chi (pi (rho (theta (iota' r B)))))[p]) W' (steps r roundCalls S) := by
  simp only [roundCalls, steps_append]
  exact stageE r hr _ _ _ (stageD r hr _ _ _ (stageC r hr _ _ _ (stageB r hr _ (parity (iota' r B)) _ _
    (stageA r hr B W S h))))

/-- The lanes before round `r`'s delayed ι. -/
def kB (B : Vector Lane 25) : Nat → Vector Lane 25
  | 0 => B
  | r + 1 => chi (pi (rho (theta (iota' r (kB B r)))))

theorem iota'_zero (B : Vector Lane 25) : iota' 0 B = B := by
  simp [iota', delayedRC]

theorem iota'_succ (B : Vector Lane 25) (r : Nat) (hr : r < 24) :
    iota' (r + 1) (kB B (r + 1)) = keccakRound ⟨r, hr⟩ (iota' r (kB B r)) := by
  have e : delayedRC (r + 1) = RC ⟨r, hr⟩ := by
    rw [delayedRC, dif_pos ⟨Nat.succ_pos r, hr⟩]; rfl
  rw [kB, keccakRound, iota, iota', e]

/-- After `n` rounds with the last ι applied: the first `n` Keccak-f rounds. -/
theorem iota'_kB (B : Vector Lane 25) : ∀ n ≤ 24,
    iota' n (kB B n) = ((List.finRange 24).take n).foldl (fun A r => keccakRound r A) B
  | 0, _ => by simp [kB, iota'_zero]
  | n + 1, h => by
    rw [iota'_succ B n (by omega), iota'_kB B n (by omega),
      List.take_add_one, List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.foldl_append]
    simp

theorem keccakF_kB (B : Vector Lane 25) : iota' 24 (kB B 24) = keccakF B := by
  rw [iota'_kB B 24 le_rfl, List.take_of_length_le (by simp)]
  rfl

end RV.Delegation
