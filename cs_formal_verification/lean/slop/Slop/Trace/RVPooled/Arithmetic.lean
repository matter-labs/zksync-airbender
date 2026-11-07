import Slop.Trace.RVPooledStep
import Slop.Trace.RVProgram
import Slop.ISA.RV.Step

/-! The standard table's ADD/SUB-family and word-memory metadata (`Trace.rvDecoderFields`), by instruction: the NOP row
    (an arithmetic write to x0 or a discarded load), one of ADD/SUB/ADDI/LUI/AUIPC with `rd ≠ x0`, or LW (`rd ≠ x0`)/SW.
    A NOP row's instruction only advances the PC (`rv_nop_exec`). -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- The standard table's NOP row (an arithmetic write to x0, or a discarded load). -/
abbrev rvNopData : DecoderData := ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩

/-- The standard table's metadata cases. -/
theorem rv_arithmetic_cases {i : RV.Instr} {d : DecoderData} (fields : Trace.rvDecoderFields i = some d) :
    d = rvNopData ∨
    (d.family = .addSub ∧ ∃ rd, rd ≠ 0 ∧ ((∃ rs1 rs2, i = .op .add rd rs1 rs2 ∨ i = .op .sub rd rs1 rs2) ∨
      (∃ rs1 imm, i = .opImm .add rd rs1 imm) ∨ (∃ imm, i = .lui rd imm ∨ i = .auipc rd imm))) ∨
    (d.family = .wordMemory ∧ ((∃ rd rs1 imm, rd ≠ 0 ∧ i = .load 4 true rd rs1 imm) ∨
      ∃ rs2 rs1 imm, i = .store 4 rs2 rs1 imm)) := by
  unfold Trace.rvDecoderFields at fields
  split at fields
  all_goals try simp only [arithmeticFields] at fields
  all_goals try split at fields
  all_goals first
    | (cases fields; done)
    | (simp only [Option.some.injEq] at fields
       subst fields
       first
         | exact Or.inl rfl
         | exact Or.inr (Or.inl ⟨rfl, _, by assumption, Or.inl ⟨_, _, Or.inl rfl⟩⟩)
         | exact Or.inr (Or.inl ⟨rfl, _, by assumption, Or.inl ⟨_, _, Or.inr rfl⟩⟩)
         | exact Or.inr (Or.inl ⟨rfl, _, by assumption, Or.inr (Or.inl ⟨_, _, rfl⟩)⟩)
         | exact Or.inr (Or.inl ⟨rfl, _, by assumption, Or.inr (Or.inr ⟨_, Or.inl rfl⟩)⟩)
         | exact Or.inr (Or.inl ⟨rfl, _, by assumption, Or.inr (Or.inr ⟨_, Or.inr rfl⟩)⟩)
         | exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨_, _, _, by assumption, rfl⟩⟩)
         | exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨_, _, _, rfl⟩⟩))

/-- An instruction with the NOP row only advances the PC (up to x0's stored value). -/
theorem rv_nop_exec (s : RV.State) {i : RV.Instr} (fields : Trace.rvDecoderFields i = some rvNopData) :
    ∃ next, RV.exec s i = some next ∧ RV.Same next s.nextInstr := by
  unfold Trace.rvDecoderFields at fields
  split at fields
  all_goals try simp only [arithmeticFields] at fields
  all_goals try split at fields
  all_goals first
    | (cases fields; done)
    | (simp only [Option.some.injEq, DecoderData.mk.injEq] at fields
       first
         | (obtain ⟨-, -, -, h, -⟩ := fields; contradiction)
         | skip)
  all_goals (obtain rfl : _ = (0 : BitVec 5) := by assumption)
  all_goals first
    | exact ⟨_, rfl, (rv_same_set_zero s _).nextInstr⟩
    | exact ⟨_, RV.exec_load_x0 s _ _ _ _, RV.Same.refl _⟩

end Airbender.Trace.Proofs
