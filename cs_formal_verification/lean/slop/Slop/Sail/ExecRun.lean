import Slop.Sail.SimpleTree
import Slop.ISA.Sail.Monad

/-! # The `hexec` obligation of `step_of_exec`, from a lean-sail run

A successful lean-sail run of `normalStep (execution input)` (the normal four-byte path around the AddSub clause)
gives `runSail` on the clause, from the state after the `nextPC := PC + 4` assignment, with the same result. -/

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem Configuration Airbender.Reference.Sail SailRV32 SailRV32.Functions Slop

/-- The `nextPC := PC + 4` assignment, as a `runSail` step. -/
theorem runSail_normalBaseNextPC (σ : SailState) :
    runSail normalBaseNextPC σ = .ok () (σ.set .nextPC (σ.regs .PC + 4)) := by
  unfold normalBaseNextPC
  simp only [runF_bind, runF_readReg, runF_writeReg]
  congr 2

/-- Splitting a successful `normalStep` run: the instruction runs from the state after `nextPC := PC + 4`,
with the same result. -/
theorem runSail_normalStep_split (m : SailM ExecutionResult) (σ σ' : SailState) (r : ExecutionResult)
    (hrun : runSail (normalStep m) σ = .ok r σ') :
    ∃ σ2, runSail m (σ.set .nextPC (σ.regs .PC + 4)) = .ok r σ2 := by
  unfold normalStep at hrun
  simp only [runF_bind, runSail_normalBaseNextPC] at hrun
  cases h : runSail m (σ.set .nextPC (σ.regs .PC + 4)) with
  | ok a s1 =>
    refine ⟨s1, ?_⟩
    rw [h] at hrun
    simp only [runF_pure] at hrun
    split at hrun <;> simp_all
  | error e s1 =>
    rw [h] at hrun
    simp at hrun

/-- The AddSub clause, run by lean-sail from `before`, is a successful `runSail` step from the state after
`nextPC := PC + 4`. -/
theorem execution_hexec (input : Input) (before after : State) (σ : SailState)
    (hA : Agrees before σ)
    (hrun : (interpretSailEffects (normalStep (execution input))).run before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after) :
    ∃ σ2, runSail (execution input) (σ.set .nextPC (σ.regs .PC + 4)) = .ok SailRV32.Functions.RETIRE_SUCCESS σ2 := by
  obtain ⟨σ', hσ', -⟩ := forward_simple _ before after σ _ (simple_normalStep (simple_execution input)) hA hrun
  exact runSail_normalStep_split _ σ σ' _ hσ'

end Airbender.Reference.RiscV.Sail
