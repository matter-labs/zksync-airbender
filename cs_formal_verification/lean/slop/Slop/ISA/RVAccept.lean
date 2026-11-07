import Human.ISA.RV32

/-! # RV acceptance of the AddSub opcodes

`RV.step` fetches at an ROM-aligned PC, decodes the word there, and executes. For ADD/SUB/ADDI/LUI/AUIPC, `exec`
never fails, so the step exists exactly when the PC is in the fetch domain and the word decodes to the instruction.
No premise beyond those two. -/

namespace RV

/-- The fetch succeeds when the PC is in the fetch domain and the word decodes to `i`; the step is `exec`. -/
theorem step_of_decode (s : State) (i : Instr) (hpc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END)
    (hdec : decode (read s.rom s.pc 4) = some i) : step s = exec s i := by
  unfold step
  rw [if_pos hpc, hdec]
  rfl

theorem step_op_add (s : State) (rd rs1 rs2 : Reg) (hpc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END)
    (hdec : decode (read s.rom s.pc 4) = some (.op .add rd rs1 rs2)) :
    step s = some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).nextInstr) := by
  rw [step_of_decode s _ hpc hdec]
  rfl

theorem step_op_sub (s : State) (rd rs1 rs2 : Reg) (hpc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END)
    (hdec : decode (read s.rom s.pc 4) = some (.op .sub rd rs1 rs2)) :
    step s = some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).nextInstr) := by
  rw [step_of_decode s _ hpc hdec]
  rfl

theorem step_opImm_add (s : State) (rd rs1 : Reg) (imm : Word) (hpc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END)
    (hdec : decode (read s.rom s.pc 4) = some (.opImm .add rd rs1 imm)) :
    step s = some ((s.setReg rd (s.getReg rs1 + imm)).nextInstr) := by
  rw [step_of_decode s _ hpc hdec]
  rfl

theorem step_lui (s : State) (rd : Reg) (imm : Word) (hpc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END)
    (hdec : decode (read s.rom s.pc 4) = some (.lui rd imm)) :
    step s = some ((s.setReg rd imm).nextInstr) := by
  rw [step_of_decode s _ hpc hdec]
  rfl

theorem step_auipc (s : State) (rd : Reg) (imm : Word) (hpc : s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ ROM_END)
    (hdec : decode (read s.rom s.pc 4) = some (.auipc rd imm)) :
    step s = some ((s.setReg rd (s.pc + imm)).nextInstr) := by
  rw [step_of_decode s _ hpc hdec]
  rfl

end RV
