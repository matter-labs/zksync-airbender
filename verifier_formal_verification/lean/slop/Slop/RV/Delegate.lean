import Slop.RV.Mem
import Slop.RV.Input

/-! Delegation calls on our spec, for any precompile: one step applies the effect; what the written words read back
as (`readWords_storeAll`) and that other words keep their value (`read_storeAll_other`). -/

namespace RV

theorem step_delegate (s t : State) (w : Word) (k : DelegationKind) (e : Effect)
    (hpc : s.pc.toNat % 4 = 0) (hrom : s.pc.toNat + 4 ≤ ROM_END) (hw : read s.mem s.pc 4 = w)
    (hd : decode w = some (.delegate k))
    (he : Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem = some e)
    (ht : s.applyEffect e = some t) : step s = some t := by
  rw [step_fetch s w hpc hrom hw, hd, Option.bind_some]
  simp only [exec, he, Option.bind_some, ht]

theorem storeAll_append (s : State) (ws ws' : List (Word × Word)) :
    s.storeAll (ws ++ ws') = (s.storeAll ws).storeAll ws' := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact ih _

/-- A word no write touches keeps its value. -/
theorem read_storeAll_other (s : State) (ws : List (Word × Word)) (b : Word) (hb : b.toNat + 4 ≤ 2 ^ 32)
    (h : ∀ aw ∈ ws, aw.1.toNat + 4 ≤ 2 ^ 32 ∧ (aw.1.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ aw.1.toNat)) :
    read (s.storeAll ws).mem b 4 = read s.mem b 4 := by
  induction ws generalizing s with
  | nil => rfl
  | cons aw ws ih =>
    obtain ⟨a, w⟩ := aw
    show read ((s.store a w 4).storeAll ws).mem b 4 = _
    rw [ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have := h (a, w) List.mem_cons_self
    exact read_write_disjoint s.mem a w b 4 4 this.2 this.1 hb

theorem writesAt_addr {n : Nat} (a : Word) (v : Vector Word n) (ha : a.toNat + 4 * n ≤ 2 ^ 32) :
    ∀ aw ∈ writesAt a v, ∃ j < n, aw.1.toNat = a.toNat + 4 * j := by
  intro aw h
  simp only [writesAt, List.mem_map, List.mem_finRange, true_and] at h
  obtain ⟨j, rfl⟩ := h
  exact ⟨j, j.isLt, by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega⟩

/-- The words of `writesAt a v`, when no later write touches them, read back as `v`. -/
theorem readWords_storeAll {n : Nat} (s : State) (pre rest : List (Word × Word)) (a : Word) (v : Vector Word n)
    (ha : a.toNat + 4 * n ≤ 2 ^ 32)
    (hrest : ∀ aw ∈ rest, aw.1.toNat + 4 ≤ 2 ^ 32 ∧ (aw.1.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 * n ≤ aw.1.toNat)) :
    readWords (s.storeAll (pre ++ writesAt a v ++ rest)).mem a n = v := by
  apply Vector.ext; intro i hi
  simp only [readWords, Vector.getElem_ofFn]
  have hai : (a + BitVec.ofNat 32 (4 * i)).toNat = a.toNat + 4 * i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  set f := fun j : Fin n => (a + BitVec.ofNat 32 (4 * j.val), v[j]) with hf
  have split : writesAt a v =
      ((List.finRange n).take i).map f ++ (a + BitVec.ofNat 32 (4 * i), v[i]) :: ((List.finRange n).drop (i + 1)).map f := by
    simp only [writesAt]
    conv_lhs => rw [← List.take_append_drop i (List.finRange n)]
    rw [List.map_append, List.drop_eq_getElem_cons (by simpa using hi)]
    simp [hf]
  rw [split, List.append_assoc, List.append_assoc, storeAll_append, storeAll_append, List.cons_append,
    show ∀ (t : State) x xs, t.storeAll (x :: xs) = (t.store x.1 x.2 4).storeAll xs from fun _ _ _ => rfl,
    read_storeAll_other _ _ _ (by omega)]
  · exact read_write_same4 _ _ _
  · intro aw hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_map] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      have hj' := (List.mem_drop_iff_getElem.mp hj)
      obtain ⟨k, hk, hjk⟩ := hj'
      simp only [List.getElem_finRange] at hjk
      subst hjk
      simp only [List.length_finRange] at hk
      rw [hai]
      simp only [hf, BitVec.toNat_add, BitVec.toNat_ofNat, Fin.coe_cast]
      omega
    · have := hrest aw hm; rw [hai]; omega

theorem storeAll_pc_regs (s : State) (ws : List (Word × Word)) :
    (s.storeAll ws).pc = s.pc ∧ (s.storeAll ws).regFile = s.regFile := by
  induction ws generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons w ws ih => exact ih _

/-- The machine state after an effect. -/
theorem applyEffect_some {s t : State} {e : Effect} (h : s.applyEffect e = some t) :
    t.mem = (s.storeAll e.writes).mem ∧ t.pc = s.pc + 4 ∧ t.input = s.input ∧
      ∀ r, t.getReg r = if r = e.reg ∧ r ≠ 0 then e.val else s.getReg r := by
  have hi := applyEffect_input h
  unfold State.applyEffect at h
  split_ifs at h
  rw [Option.some.injEq] at h
  subst h
  obtain ⟨hp, hr⟩ := storeAll_pc_regs s e.writes
  refine ⟨rfl, by simp [State.nextInstr, State.setReg, hp], hi, fun r => ?_⟩
  simp only [State.getReg, State.nextInstr, State.setReg, hr]
  by_cases h0 : r = 0 <;> by_cases h1 : r = e.reg <;> simp_all

end RV
