import Airbender.Review.Sail
import Airbender.Proofs.Sail.Sequential
import Airbender.Proofs.Arithmetic.Word
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

private theorem primitive_write_injective (reg : SailRV32.Register)
    (left right : SailRV32.RegisterType reg) (state : State)
    (h : run (do SailRV32.writeReg reg left; pure SailRV32.Functions.RETIRE_SUCCESS) state =
      run (do SailRV32.writeReg reg right; pure SailRV32.Functions.RETIRE_SUCCESS) state) :
    left = right := by
  change EStateM.Result.ok SailRV32.Functions.RETIRE_SUCCESS
      { state with regs := state.regs.insert reg left } =
    EStateM.Result.ok SailRV32.Functions.RETIRE_SUCCESS
      { state with regs := state.regs.insert reg right } at h
  have hs := (EStateM.Result.ok.inj h).2
  have hg := congrArg (fun s : State => s.regs.get? reg) hs
  simpa using hg

set_option maxHeartbeats 800000 in
/-- Equal successful writes to a nonzero destination imply equal native words. -/
private theorem writeResult_injective (input : Input) {left right : Word}
    (hnz : input.rd ≠ .Regidx (0 : BitVec 5))
    (h : run (writeResult input left) input.before =
      run (writeResult input right) input.before) : left.toBitVec = right.toBitVec := by
  cases hd : input.rd with
  | Regidx bits =>
    have hb : bits.toNat < 32 := bits.isLt
    have hne : bits.toNat ≠ 0 := by
      intro hz
      apply hnz
      rw [hd]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simpa using hz
    simp only [writeResult, hd, SailRV32.Functions.wX_bits] at h
    change run (do SailRV32.Functions.wX (.Regno (bits.toNat : Int)) left.toBitVec
                   pure SailRV32.Functions.RETIRE_SUCCESS) input.before =
      run (do SailRV32.Functions.wX (.Regno (bits.toNat : Int)) right.toBitVec
              pure SailRV32.Functions.RETIRE_SUCCESS) input.before at h
    interval_cases bits.toNat
    all_goals
      first
      | exact False.elim (hne rfl)
      | simp only [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
          write_callback_pure, freeM_pure_bind] at h
        exact primitive_write_injective _ _ _ _ h

/-- Reusable uniqueness of the Sail specification, independent of any circuit equations. -/
theorem spec_deterministic {input : Input} {left right : Word}
    (hnz : input.rd ≠ .Regidx (0 : BitVec 5))
    (hl : left.Bounded) (hr : right.Bounded)
    (sl : spec input left) (sr : spec input right) : left = right := by
  obtain ⟨afterL, execL, writeL⟩ := sl
  obtain ⟨afterR, execR, writeR⟩ := sr
  have hs : afterL = afterR := (EStateM.Result.ok.inj (execL.symm.trans execR)).2
  exact Word.eq_of_toBitVec_eq hl hr
    (writeResult_injective input hnz (writeL.trans (hs ▸ writeR.symm)))

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
