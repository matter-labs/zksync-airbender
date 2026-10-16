import Slop.RV.Step

/-! The input (CSR 0x7c0) and runs that read none of it: a run that succeeds with the input empty reads nothing and
runs the same with any input (`run_lift`). So no contract (`Returns`, …) needs to mention the input. -/

namespace RV

/-- The state with input `t`. -/
def State.withInput (s : State) (t : List Word) : State := { s with input := t }

@[simp] theorem withInput_pc (s : State) (t : List Word) : (s.withInput t).pc = s.pc := Eq.trans rfl rfl
@[simp] theorem withInput_mem (s : State) (t : List Word) : (s.withInput t).mem = s.mem := Eq.trans rfl rfl
@[simp] theorem withInput_input (s : State) (t : List Word) : (s.withInput t).input = t := Eq.trans rfl rfl
@[simp] theorem withInput_getReg (s : State) (t : List Word) (r : Reg) :
    (s.withInput t).getReg r = s.getReg r := Eq.trans rfl rfl

theorem storeAll_input (s : State) (ws : List (Word × Word)) : (s.storeAll ws).input = s.input := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact (ih _).trans rfl

theorem storeAll_withInput (s : State) (ws : List (Word × Word)) (t : List Word) :
    (s.withInput t).storeAll ws = (s.storeAll ws).withInput t := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact ih (s.store w.1 w.2 4)

theorem applyEffect_input {s t : State} {e : Effect} (h : s.applyEffect e = some t) : t.input = s.input := by
  unfold State.applyEffect at h
  split_ifs at h; cases h
  exact storeAll_input _ _

theorem applyEffect_withInput (s : State) (e : Effect) (t : List Word) :
    (s.withInput t).applyEffect e = (s.applyEffect e).map (·.withInput t) := by
  unfold State.applyEffect
  split_ifs
  · simp only [storeAll_withInput, Option.map_some]; rfl
  · rfl

/-- Only the input read moves the input. -/
theorem exec_keeps_input {s t : State} {i : Instr} (hex : exec s i = some t) (hi : i.readsInput = false) :
    t.input = s.input := by
  cases i
  case delegate k =>
    simp only [exec] at hex
    obtain ⟨e, -, he⟩ := Option.bind_eq_some_iff.mp hex
    exact applyEffect_input he
  all_goals simp only [Instr.readsInput, reduceCtorEq] at hi
  all_goals simp only [exec, State.jumpAligned] at hex
  all_goals (repeat' split at hex) <;> simp_all [Option.map, State.setReg, State.nextInstr, State.setPC,
      State.store] <;> (subst_vars; simp)

/-- … and the other instructions do not look at it. -/
theorem exec_input_irrel (s : State) (i : Instr) (hi : i.readsInput = false) (t : List Word) :
    exec (s.withInput t) i = (exec s i).map (·.withInput t) := by
  cases i
  case delegate k =>
    simp only [exec, withInput_getReg, withInput_mem]
    cases Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem with
    | none => rfl
    | some e => exact applyEffect_withInput s e t
  all_goals simp only [Instr.readsInput, reduceCtorEq] at hi
  all_goals simp only [exec, State.withInput, State.jumpAligned, State.getReg, State.setReg, State.nextInstr,
      State.setPC, State.store]
  all_goals (repeat' split) <;> simp_all

/-- One step with the input empty: no input read, and the same step with any input. -/
theorem step_lift {s s' : State} (h : step s = some s') (he : s.input = []) :
    s'.input = [] ∧ ∀ t, step (s.withInput t) = some (s'.withInput t) := by
  unfold step at h
  by_cases hc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END
  case neg => rw [if_neg hc] at h; cases h
  rw [if_pos hc] at h
  obtain ⟨i, hdec, hex⟩ := Option.bind_eq_some_iff.mp h
  cases hr : i.readsInput
  · refine ⟨(exec_keeps_input hex hr).trans he, fun t => ?_⟩
    show (if s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END then
      (decode (read s.mem s.pc 4)).bind (exec (s.withInput t)) else none) = _
    rw [if_pos hc, hdec, Option.bind_some, exec_input_irrel s i hr t, hex]; rfl
  · obtain ⟨rd, rfl⟩ : ∃ rd, i = .inputRead rd := by cases i <;> simp_all [Instr.readsInput]
    simp [exec, he] at hex

/-- A run with the input empty: it reads no input, and runs the same with any input. -/
theorem run_lift : ∀ (k : Nat) (s s' : State), run k s = some s' → s.input = [] →
    s'.input = [] ∧ ∀ t, run k (s.withInput t) = some (s'.withInput t)
  | 0, s, s', h, he => by
    simp only [run, Option.some.injEq] at h; subst h; exact ⟨he, fun _ => rfl⟩
  | k + 1, s, s', h, he => by
    obtain ⟨s1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e1, l1⟩ := step_lift h1 he
    obtain ⟨e, l⟩ := run_lift k s1 s' h e1
    refine ⟨e, fun t => ?_⟩
    simp only [run, l1 t, Option.bind_some]
    exact l t

end RV

namespace RV


/-- The input read `csrrw rd, 0x7c0, x0` at the PC: `rd` gets the next input word. -/
theorem step_read (s : State) (w : Word) (rd : Reg) (v : Word) (rest : List Word)
    (hpc : s.pc.toNat % 4 = 0) (hrom : s.pc.toNat + 4 ≤ ROM_END) (hw : read s.mem s.pc 4 = w)
    (hd : decode w = some (.inputRead rd)) (hin : s.input = v :: rest) :
    step s = some ((s.setReg rd v).nextInstr.withInput rest) := by
  rw [step_fetch s w hpc hrom hw, hd, Option.bind_some]
  simp only [exec, hin]; rfl

end RV
