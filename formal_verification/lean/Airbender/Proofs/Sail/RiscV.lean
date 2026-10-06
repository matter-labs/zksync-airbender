import Airbender.Review.Sail
import Airbender.Proofs.Sail.Sequential
import Mathlib.Tactic.IntervalCases

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open Airbender.Arithmetic
open _root_.Sail.ArchSem

private theorem write_callback_pure (reg : SailRV32.regidx) (value : BitVec 32) :
    SailRV32.Functions.xreg_write_callback reg value = pure () := by
  cases reg
  simp [SailRV32.Functions.xreg_write_callback, SailRV32.Functions.reg_name_forwards,
    SailRV32.Functions.encdec_reg_forwards_matches, SailRV32.Functions.get_config_use_abi_names,
    SailRV32.Functions.not, SailRV32.Functions.xreg_full_write_callback, freeM_pure_bind]

private theorem primitive_write (reg : SailRV32.Register) (value : SailRV32.RegisterType reg)
    (state : State) :
    run (do SailRV32.writeReg reg value; pure ()) state =
      .ok () { state with regs := state.regs.insert reg value } := rfl

private theorem run_pure (state : State) :
    run (pure () : SailRV32.SailM Unit) state = .ok () state := rfl

private theorem write_success (rd : SailRV32.regidx) (value : BitVec 32) (state : State) :
    ∃ after, run (SailRV32.Functions.wX_bits rd value) state = .ok () after := by
  cases rd with
  | Regidx bits =>
    have hb : bits.toNat < 32 := bits.isLt
    change ∃ after, run (SailRV32.Functions.wX (.Regno (bits.toNat : Int)) value) state = _
    interval_cases bits.toNat <;>
      simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
        write_callback_pure, freeM_pure_bind, primitive_write, run_pure]

/-- Connect a proved result equation to the actual generated execution clauses.
    This lemma introduces no separate instruction-specification relation. -/
theorem spec_of_result {input : Input} {output : Word} (hc : Contract input)
    (h : output.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec) :
    spec input output := by
  have he : run (execution input) input.before = run (writeResult input output) input.before := by
    unfold execution writeResult
    cases hop : input.row.opcode
    · simp only [hop, SailRV32.Functions.execute_RTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ hc.leftRead]
      rw [run_bind_of_ok _ _ _ _ _ (hc.rightRead (by simp [hop]))]
      rw [← h]
    · simp only [hop, SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ hc.leftRead]
      rw [← hc.signExtension hop, ← h]
    · simp only [hop, SailRV32.Functions.execute_RTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ hc.leftRead]
      rw [run_bind_of_ok _ _ _ _ _ (hc.rightRead (by simp [hop]))]
      rw [← h]
  obtain ⟨after, hw⟩ := write_success input.rd output.toBitVec input.before
  have hw' : run (writeResult input output) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold writeResult
    rw [run_bind_of_ok _ _ _ _ _ hw]
    rfl
  exact ⟨after, he.trans hw', hw'⟩

end Airbender.Reference.RiscV.Sail
