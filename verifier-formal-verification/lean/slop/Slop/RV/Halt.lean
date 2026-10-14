import Slop.RV.Step

/-! The halt loop `j .` (`jal x0, 0`): once there, every later step keeps the PC and all registers. -/

namespace RV

theorem halt_forever (s : State) (hal : s.pc.toNat % 4 = 0) (hrom : s.pc.toNat + 4 ≤ ROM_END)
    (hw : read s.mem s.pc 4 = 0x0000006f#32) :
    ∀ k, ∃ s'', run k s = some s'' ∧ s''.pc = s.pc ∧ ∀ i, s''.getReg i = s.getReg i := by
  intro k
  induction k generalizing s with
  | zero => exact ⟨s, rfl, rfl, fun _ => rfl⟩
  | succ k ih =>
    have hd : decode 0x0000006f#32 = some (.jal 0 0) := rfl
    have hst : step s = some ((s.jump (s.pc + 0)).setReg 0 (s.pc + 4)) := by
      rw [step_ok s hal hrom, hw, hd, Option.bind_some, exec_jal _ _ _ (by simpa using hal)]
    obtain ⟨s'', hrun, hpc, hr⟩ := ih ((s.jump (s.pc + 0)).setReg 0 (s.pc + 4))
      (by simpa using hal) (by simpa using hrom) (by simpa using hw)
    refine ⟨s'', by simp only [run, hst, Option.bind_some, hrun], by simpa using hpc, fun i => ?_⟩
    rw [hr i, r_set]
    by_cases h : i = 0
    · subst h; exact (r_zero s).symm
    · simp only [h, ↓reduceIte, jump_r]

end RV
