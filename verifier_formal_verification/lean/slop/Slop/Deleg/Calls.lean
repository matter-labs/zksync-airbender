import Slop.RV.BlakeDeleg.Rounds
import Human.DelegationRuns

/-! Runs of delegation calls (`calls`): one call writing inside a buffer, composing runs, reading what they wrote. -/

namespace RV
set_option linter.unusedSimpArgs false

theorem calls_append (ks ks' : List DelegationKind) (s : State) :
    calls (ks ++ ks') s = (calls ks s).bind (calls ks') := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.cons_append, calls]
    cases (Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem).bind s.applyEffect <;> simp [ih]

theorem calls_replicate_succ (n : Nat) (k : DelegationKind) (s : State) :
    calls (.replicate (n + 1) k) s = (calls (.replicate n k) s).bind (calls [k]) := by
  rw [List.replicate_succ', calls_append]

theorem ChangesOnly.refl (s : State) (a : Word) (n : Nat) (r : Reg) : ChangesOnly s s a n r :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem ChangesOnly.trans {s t u : State} {a : Word} {n : Nat} {r : Reg} (h1 : ChangesOnly s t a n r)
    (h2 : ChangesOnly t u a n r) : ChangesOnly s u a n r :=
  ⟨fun b hb => (h2.1 b hb).trans (h1.1 b hb), fun i hi => (h2.2 i hi).trans (h1.2 i hi)⟩

/-- Words outside the changed bytes read the same. -/
theorem ChangesOnly.readWords {s t : State} {a : Word} {N : Nat} {r : Reg} (h : ChangesOnly s t a N r) (b : Word)
    (m : Nat) (hb : b.toNat + 4 * m ≤ 2 ^ 32) (ho : b.toNat + 4 * m ≤ a.toNat ∨ a.toNat + N ≤ b.toNat) :
    RV.readWords t.mem b m = RV.readWords s.mem b m := by
  apply Vector.ext; intro i hi
  simp only [RV.readWords, Vector.getElem_ofFn]
  exact read_congr _ _ _ _ fun j hj => h.1 _ (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

/-- One call whose writes are aligned words inside `[a, a + N)` in RAM. -/
theorem calls_one {s : State} {k : DelegationKind} {e : Effect}
    (he : Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem = some e) (a : Word) (N : Nat)
    (hN : a.toNat + N ≤ RAM_END) (hR : e.reg ≠ 0)
    (hw : ∀ aw ∈ e.writes, ROM_END ≤ aw.1.toNat ∧ aw.1.toNat % 4 = 0 ∧ a.toNat ≤ aw.1.toNat ∧
      aw.1.toNat + 4 ≤ a.toNat + N) :
    ∃ t, calls [k] s = some t ∧ t.mem = (s.storeAll e.writes).mem ∧ ChangesOnly s t a N e.reg ∧
      t.getReg e.reg = e.val := by
  have happ : ∃ t, s.applyEffect e = some t := by
    unfold State.applyEffect
    rw [if_pos (List.all_eq_true.mpr fun aw haw => decide_eq_true (by
      have := hw aw haw; simp only [writable, aligned, ROM_END, RAM_END] at *; omega))]
    exact ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := happ
  obtain ⟨m', -, -, rg'⟩ := applyEffect_some ht
  refine ⟨t, by simp only [calls]; erw [he]; simp [ht], m', ⟨fun b hb => ?_, fun i hi => ?_⟩, by rw [rg', if_pos ⟨rfl, hR⟩]⟩
  · rw [m', storeAll_mem_other s _ b fun aw haw => by
      have := hw aw haw; simp only [ROM_END, RAM_END] at *; omega]
  · rw [rg', if_neg fun h => hi h.1]

/-- Where `writesAt a v` writes. -/
theorem writesAt_in {n : Nat} (a : Word) (v : Vector Word n) (h1 : ROM_END ≤ a.toNat) (h2 : a.toNat % 4 = 0)
    (h3 : a.toNat + 4 * n ≤ RAM_END) :
    ∀ aw ∈ writesAt a v, ROM_END ≤ aw.1.toNat ∧ aw.1.toNat % 4 = 0 ∧ a.toNat ≤ aw.1.toNat ∧
      aw.1.toNat + 4 ≤ a.toNat + 4 * n := by
  intro aw h
  obtain ⟨j, hj, e⟩ := writesAt_addr a v (by simp only [RAM_END] at h3; omega) aw h
  omega

theorem readWords_writesAt {n : Nat} (s : State) (a : Word) (v : Vector Word n) (ha : a.toNat + 4 * n ≤ 2 ^ 32) :
    RV.readWords (s.storeAll (writesAt a v)).mem a n = v := by
  simpa using readWords_storeAll s [] [] a v ha (by simp)

/-- `m` words from word `i` on. -/
theorem readWords_sub (mem : Word → BitVec 8) (a : Word) (n i m : Nat) (h : i + m ≤ n) :
    RV.readWords mem (a + BitVec.ofNat 32 (4 * i)) m = Vector.ofFn fun j : Fin m => (RV.readWords mem a n)[i + j.val] := by
  apply Vector.ext; intro j hj
  simp only [RV.readWords, Vector.getElem_ofFn]
  congr 1
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem calls_run : CallsRun := by
  intro k w n
  induction n with
  | zero => intro s t _ _ _ _ h; exact h
  | succ n ih =>
    intro s t hd hpc hrom hw h
    simp only [List.replicate_succ, calls] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, he, ha⟩ := Option.bind_eq_some_iff.mp h1
    have hstep : step s = some s1 := step_delegate s s1 w k e hpc (by omega)
      (by simpa using hw 0 (by omega)) hd he ha
    obtain ⟨m1, pc1, -, -⟩ := applyEffect_some ha
    have hok : ∀ aw ∈ e.writes, writable aw.1 4 ∧ aligned aw.1 4 := by
      unfold State.applyEffect at ha
      split_ifs at ha with hc
      exact fun aw haw => of_decide_eq_true (List.all_eq_true.mp hc aw haw)
    have hrom1 : ∀ b : Word, b.toNat < ROM_END → s1.mem b = s.mem b := fun b hb => by
      rw [m1, storeAll_mem_other s _ b fun aw haw => by
        have := hok aw haw; simp only [writable, aligned, ROM_END, RAM_END] at this hb ⊢; omega]
    have hpc1 : s1.pc.toNat = s.pc.toNat + 4 := by
      rw [pc1, BitVec.toNat_add]; simp only [ROM_END] at hrom; simp; omega
    rw [run_succ, hstep, Option.bind_some]
    refine ih s1 t hd (by omega) (by omega) (fun i hi => ?_) h2
    rw [read_congr s1.mem s.mem _ 4 fun j hj => hrom1 _ (by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hpc1]; simp only [ROM_END] at hrom ⊢; omega)]
    rw [← hw (i + 1) (by omega)]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hpc1]; simp only [ROM_END] at hrom; omega

end RV
