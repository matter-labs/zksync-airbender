import Slop.ISA.Equiv.Regs

/-! The assumptions of the Sail equivalence claims can be met (`Human/ISA/Sail/Theorems.lean`): a word of the spec's
table with a configured Sail state, and an RV state that agrees with an Airbender machine and has a next state. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv.NonVacuous

/-- The bytes of the word `x`, repeated at every aligned address. -/
def pattern (x : BitVec 32) (n : Nat) : BitVec 8 := x.extractLsb' (8 * (n % 4)) 8

/-- Sail's reset state at PC 0 with `addi x0, x0, 0` at every aligned address. -/
noncomputable def sail : SailState :=
  { Airbender.resetState.set .PC (0 : BitVec 32) with mem := pattern 0x00000013#32 }

/-- The RV state that `sail` shows a program: PC 0, Sail's registers, the same bytes in ROM and RAM. -/
noncomputable def state : RV.State where
  pc := 0
  regFile := fun i => xget sail i
  rom := fun a => pattern 0x00000013#32 a.toNat
  mem := fun a => pattern 0x00000013#32 a.toNat

theorem configured : Airbender.Configured sail := by
  intro r h
  simp only [sail, SailState.set]
  split
  · rename_i e
    subst e
    simp [Airbender.writtenByProgram] at h
  · rfl

theorem agree : Airbender.Agree state ⟨sail, state.mem, state.input⟩ := by
  refine ⟨⟨configured, ?_, ?_, ?_⟩, fun _ _ => rfl, rfl⟩
  · simp [sail, state, SailState.set]
  · intro i
    rw [reg_eq]
    simp only [RV.State.getReg, state]
    split
    · rename_i e
      subst e
      rfl
    · rfl
  · intro a
    simp only [RV.State.loadView, state, sail]
    split <;> rfl

theorem decode_assumptions :
    ∃ word instr σ, RV.decode word = some instr ∧ Airbender.Configured σ :=
  ⟨0x00000013#32, _, Airbender.resetState, (Option.some_get (by decide)).symm, fun _ _ => rfl⟩

theorem step_assumptions :
    ∃ s s' m, Airbender.Agree s m ∧ RV.step s = some s' :=
  ⟨state, _, _, agree, (Option.some_get (by decide)).symm⟩

end Slop.Equiv.NonVacuous
