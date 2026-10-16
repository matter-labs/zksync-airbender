import Slop.RV.Step

/-! Runs in sequence, and the state after a call instruction (`jal ra, …`). -/

namespace RV

theorem run_trans {a b : Nat} {S S1 S2 : State} (h1 : run a S = some S1) (h2 : run b S1 = some S2) :
    run (a + b) S = some S2 := by
  rw [run_add, h1, Option.bind_some, h2]

/-- The state after a call instruction: registers other than `ra` as before. -/
theorem jal_getReg (T : State) (t v : Word) (r : Reg) (hr : r ≠ 1#5) :
    ((T.setPC t).setReg 1#5 v).getReg r = T.getReg r := by
  rw [r_set, jump_r]; simp only [hr, ite_false]
  split
  · next h => subst h; rfl
  · rfl

theorem jal_getReg1 (T : State) (t v : Word) : ((T.setPC t).setReg 1#5 v).getReg 1#5 = v := by
  rw [r_set]; rfl

theorem jal_mem (T : State) (t v : Word) : ((T.setPC t).setReg 1#5 v).mem = T.mem := by
  rw [set_mem, jump_mem]

theorem jal_pc (T : State) (t v : Word) : ((T.setPC t).setReg 1#5 v).pc = t := rfl

end RV
