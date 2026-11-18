module
public import Human.ISA.RV32

@[expose] public section

/-! `RV.Same` (agreement on everything a program sees) is a congruence for `RV.exec` and `RV.step`: x0's
    stored value is never read (`getReg` reads x0 as 0). -/

namespace RV

theorem Same.refl (s : State) : Same s s := ⟨rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem Same.symm {s t : State} (h : Same s t) : Same t s :=
  ⟨h.1.symm, fun i => (h.2.1 i).symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem Same.trans {s t u : State} (h : Same s t) (k : Same t u) : Same s u :=
  ⟨h.1.trans k.1, fun i => (h.2.1 i).trans (k.2.1 i), h.2.2.1.trans k.2.2.1, h.2.2.2.1.trans k.2.2.2.1,
    h.2.2.2.2.trans k.2.2.2.2⟩

theorem Same.setReg {s t : State} (h : Same s t) (rd : Reg) (v : Word) :
    Same (s.setReg rd v) (t.setReg rd v) := by
  refine ⟨h.1, fun i => ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have hi := h.2.1 i
  simp only [State.getReg, State.setReg] at hi ⊢
  split_ifs <;> simp_all

theorem Same.nextInstr {s t : State} (h : Same s t) : Same s.nextInstr t.nextInstr :=
  ⟨by simp [State.nextInstr, h.1], h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem Same.setPC {s t : State} (h : Same s t) (pc : Word) : Same (s.setPC pc) (t.setPC pc) :=
  ⟨rfl, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem Same.store {s t : State} (h : Same s t) (a v : Word) (n : Nat) :
    Same (s.store a v n) (t.store a v n) :=
  ⟨h.1, h.2.1, h.2.2.1, by simp [State.store, h.2.2.2.1], h.2.2.2.2⟩

theorem Same.storeAll {s t : State} (h : Same s t) (ws : List (Word × Word)) :
    Same (s.storeAll ws) (t.storeAll ws) := by
  induction ws generalizing s t with
  | nil => exact h
  | cons aw ws ih => exact ih (h.store aw.1 aw.2 4)

/-- Agreement of the optional results of two computations: both fail, or both succeed with agreeing states. -/
def SameOpt : Option State → Option State → Prop
  | none, none => True
  | some s, some t => Same s t
  | _, _ => False

theorem SameOpt.some_left {a b : Option State} (h : SameOpt a b) {s : State} (hs : a = some s) :
    ∃ t, b = some t ∧ Same s t := by
  subst hs
  cases b with
  | none => exact h.elim
  | some t => exact ⟨t, rfl, h⟩

theorem Same.jumpAligned {s t : State} (h : Same s t) (pc : Word) :
    SameOpt (s.jumpAligned pc) (t.jumpAligned pc) := by
  unfold State.jumpAligned
  split
  · exact h.setPC pc
  · trivial

theorem SameOpt.map {a b : Option State} (h : SameOpt a b) {f g : State → State}
    (hf : ∀ s t, Same s t → Same (f s) (g t)) : SameOpt (a.map f) (b.map g) := by
  cases a <;> cases b <;> first | trivial | exact hf _ _ h

theorem Same.applyEffect {s t : State} (h : Same s t) (e : Effect) :
    SameOpt (s.applyEffect e) (t.applyEffect e) := by
  unfold State.applyEffect
  split
  · exact ((h.storeAll e.writes).setReg e.reg e.val).nextInstr
  · trivial

theorem exec_same {s t : State} (h : Same s t) (i : Instr) : SameOpt (exec s i) (exec t i) := by
  obtain ⟨hpc, hreg, hrom, hmem, hinput⟩ := h
  have h : Same s t := ⟨hpc, hreg, hrom, hmem, hinput⟩
  have hload : s.loadView = t.loadView := by
    funext a; simp only [State.loadView, hrom, hmem]
  cases i with
  | lui rd imm => exact (h.setReg rd imm).nextInstr
  | auipc rd imm => simp only [exec, hpc]; exact (h.setReg rd _).nextInstr
  | jal rd offset =>
    simp only [exec, hpc]
    exact (h.jumpAligned _).map (fun _ _ k => k.setReg rd _)
  | jalr rd rs1 offset =>
    simp only [exec, hpc, hreg]
    exact (h.jumpAligned _).map (fun _ _ k => k.setReg rd _)
  | branch cond rs1 rs2 offset =>
    simp only [exec, hpc, hreg]
    split
    · exact h.jumpAligned _
    · exact h.nextInstr
  | load numBytes signed rd rs1 offset =>
    simp only [exec, hreg, hload]
    split
    · exact h.nextInstr
    · split
      · exact (h.setReg rd _).nextInstr
      · trivial
  | store numBytes rs2 rs1 offset =>
    simp only [exec, hreg]
    split
    · exact (h.store _ _ _).nextInstr
    · trivial
  | opImm op rd rs1 imm => simp only [exec, hreg]; exact (h.setReg rd _).nextInstr
  | op op rd rs1 rs2 => simp only [exec, hreg]; exact (h.setReg rd _).nextInstr
  | mop op rd rs1 rs2 => simp only [exec, hreg]; exact (h.setReg rd _).nextInstr
  | rev8 rd rs1 => simp only [exec, hreg]; exact (h.setReg rd _).nextInstr
  | xorRot n rd rs1 => simp only [exec, hreg]; exact (h.setReg rd _).nextInstr
  | inputRead rd =>
    simp only [exec, hinput]
    split
    · rename_i w rest _
      exact ⟨by simp [State.nextInstr, State.setReg, hpc], (h.setReg rd w).2.1, hrom, hmem, rfl⟩
    · trivial
  | inputWrite src => exact h.nextInstr
  | delegate k =>
    simp only [exec, hreg, State.delegationRAM, hmem]
    cases Delegation.effect k (t.getReg 10) (t.getReg 11) (t.getReg 12) t.mem with
    | none => trivial
    | some e => exact h.applyEffect e

theorem step_same {s t : State} (h : Same s t) : SameOpt (step s) (step t) := by
  unfold step
  rw [h.1, h.2.2.1]
  split
  · cases decode (read t.rom t.pc 4) with
    | none => trivial
    | some i => exact exec_same h i
  · trivial

end RV
