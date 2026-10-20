import Slop.RV.Stuck
import Human.SpecMerkle

/-! `merkle_check`'s frame (`MFrame`) and end (`McFinal`): the interface between its parts (the start, `Check`; the
loop, `Loop`; the end, `Exit`), so they build in parallel. -/

namespace RV
open Spec

/-- `MERKLE`, the evaluator of the path. -/
abbrev MERKLE : Word := 0x1401100#32

/-- What `merkle_check` ends with, from its start `s0` (frame `F` bytes), the node it computed and the root it
read: matching, it returns (input left: `rest`); differing, the run is stuck in `zksync_os_finish_error`. -/
def McFinal (s0 : State) (F len : Nat) (node root : Vector Word 8) (rest : List Word) (T : State) : Prop :=
  (node = root → T.pc = s0.getReg 1#5 ∧ (∀ i, calleeSaved i → T.getReg i = s0.getReg i) ∧ T.input = rest ∧
    ∀ a : Word, a.toNat + F < (s0.getReg 2#5).toNat ∨ (s0.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < MERKLE.toNat ∨ MERKLE.toNat + len ≤ a.toNat → T.mem a = s0.mem a) ∧
  (node ≠ root → AtFinishError T)

/-- `merkle_check`'s frame (`sp = sp₀ - 96`, `s1 = MERKLE`, `s10 = MERKLE - 0x100`), the registers it saved
there, the root in `s9 … s2` (as read), memory outside the frame and `MERKLE` and ROM as at the start `s0`. -/
structure MFrame (s0 : State) (F len : Nat) (root : Vector Word 8) (E : State) : Prop where
  sp : E.getReg 2#5 = s0.getReg 2#5 + 4294967200#32
  s10 : E.getReg 26#5 = 0x1401000#32
  r0 : E.getReg 25#5 = root[0]
  r1 : E.getReg 24#5 = root[1]
  r2 : E.getReg 23#5 = root[2]
  r3 : E.getReg 22#5 = root[3]
  r4 : E.getReg 20#5 = root[4]
  r5 : E.getReg 21#5 = root[5]
  r6 : E.getReg 19#5 = root[6]
  r7 : E.getReg 18#5 = root[7]
  v1 : read E.mem (s0.getReg 2#5 + 4294967292#32) 4 = s0.getReg 1#5
  v8 : read E.mem (s0.getReg 2#5 + 4294967288#32) 4 = s0.getReg 8#5
  v9 : read E.mem (s0.getReg 2#5 + 4294967284#32) 4 = s0.getReg 9#5
  v18 : read E.mem (s0.getReg 2#5 + 4294967280#32) 4 = s0.getReg 18#5
  v19 : read E.mem (s0.getReg 2#5 + 4294967276#32) 4 = s0.getReg 19#5
  v20 : read E.mem (s0.getReg 2#5 + 4294967272#32) 4 = s0.getReg 20#5
  v21 : read E.mem (s0.getReg 2#5 + 4294967268#32) 4 = s0.getReg 21#5
  v22 : read E.mem (s0.getReg 2#5 + 4294967264#32) 4 = s0.getReg 22#5
  v23 : read E.mem (s0.getReg 2#5 + 4294967260#32) 4 = s0.getReg 23#5
  v24 : read E.mem (s0.getReg 2#5 + 4294967256#32) 4 = s0.getReg 24#5
  v25 : read E.mem (s0.getReg 2#5 + 4294967252#32) 4 = s0.getReg 25#5
  v26 : read E.mem (s0.getReg 2#5 + 4294967248#32) 4 = s0.getReg 26#5
  v27 : read E.mem (s0.getReg 2#5 + 4294967244#32) 4 = s0.getReg 27#5
  mem : ∀ a : Word, a.toNat + F < (s0.getReg 2#5).toNat ∨ (s0.getReg 2#5).toNat ≤ a.toNat →
    a.toNat < MERKLE.toNat ∨ MERKLE.toNat + len ≤ a.toNat → E.mem a = s0.mem a
  rom : ∀ b : Word, b.toNat < ROM_END → E.mem b = s0.mem b

/-- The frame facts survive steps that change neither memory nor the frame's registers. -/
theorem MFrame.of_eq {s0 E E' : State} {F len : Nat} {root : Vector Word 8} (h : MFrame s0 F len root E)
    (hm : E'.mem = E.mem) (hr : ∀ r : Reg, r = 2#5 ∨ r = 26#5 ∨ r = 25#5 ∨ r = 24#5 ∨ r = 23#5 ∨ r = 22#5 ∨
      r = 21#5 ∨ r = 20#5 ∨ r = 19#5 ∨ r = 18#5 → E'.getReg r = E.getReg r) : MFrame s0 F len root E' := by
  have hr' := hr
  obtain ⟨a, b, c, d, e, f, g, i, j, k, v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, m, rom⟩ := h
  have R : ∀ r : Reg, r = 2#5 ∨ r = 26#5 ∨ r = 25#5 ∨ r = 24#5 ∨ r = 23#5 ∨ r = 22#5 ∨ r = 21#5 ∨ r = 20#5 ∨
      r = 19#5 ∨ r = 18#5 → ∀ w, E.getReg r = w → E'.getReg r = w := fun r hr w hw => (hr' r hr).trans hw
  exact ⟨R _ (by simp) _ a, R _ (by simp) _ b, R _ (by simp) _ c, R _ (by simp) _ d, R _ (by simp) _ e,
    R _ (by simp) _ f, R _ (by simp) _ g, R _ (by simp) _ i, R _ (by simp) _ j, R _ (by simp) _ k,
    by rw [hm]; exact v1, by rw [hm]; exact v8, by rw [hm]; exact v9, by rw [hm]; exact v18, by rw [hm]; exact v19,
    by rw [hm]; exact v20, by rw [hm]; exact v21, by rw [hm]; exact v22, by rw [hm]; exact v23, by rw [hm]; exact v24,
    by rw [hm]; exact v25, by rw [hm]; exact v26, by rw [hm]; exact v27,
    fun x hx hy => by rw [hm]; exact m x hx hy, fun x hx => by rw [hm]; exact rom x hx⟩

end RV
