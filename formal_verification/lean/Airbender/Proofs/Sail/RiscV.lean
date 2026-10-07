import Airbender.Review.Sail
import Airbender.Proofs.Sail.Sequential
import Mathlib.Tactic.IntervalCases

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open Airbender.Arithmetic
open _root_.Sail.ArchSem

theorem write_callback_pure (reg : SailRV32.regidx) (value : BitVec 32) :
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

theorem write_success (rd : SailRV32.regidx) (value : BitVec 32) (state : State) :
    ∃ after, run (SailRV32.Functions.wX_bits rd value) state = .ok () after := by
  cases rd with
  | Regidx bits =>
    have hb : bits.toNat < 32 := bits.isLt
    change ∃ after, run (SailRV32.Functions.wX (.Regno (bits.toNat : Int)) value) state = _
    interval_cases bits.toNat <;>
      simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
        write_callback_pure, freeM_pure_bind, primitive_write, run_pure]

/-- Internal execution-only relation, used to compose destination and PC effects. -/
def destinationSpec (input : Input) (output : Word) : Prop :=
  ∃ after,
    run (execution input) input.before = .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
    run (writeResult input.rd output) input.before = .ok SailRV32.Functions.RETIRE_SUCCESS after

/-- Sail's actual x0 accessor discards the value and performs no state update. -/
theorem write_zero (value : BitVec 32) :
    SailRV32.Functions.wX_bits zeroRegister value = pure () := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, _root_.Sail.BitVec.toNatInt,
    freeM_pure_bind]

/-- An original instruction writing x0 leaves the state unchanged, even when its
    circuit operands were replaced by zero. Only successful original reads are required. -/
theorem spec_zero_write {input : Input} {output : Word} (hc : Contract input)
    (hz : input.rd = zeroRegister) : destinationSpec input output := by
  have executed : run (execution input) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS input.before := by
    cases hop : input.row.opcode
    · obtain ⟨left, hl, _⟩ := hc.leftRead (by simp [hop])
      obtain ⟨right, hr, _⟩ := hc.rightRead (by simp [hop])
      simp only [execution, hop, SailRV32.Functions.execute_RTYPE, hz,
        freeM_bind_assoc, freeM_pure_bind]
      rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr]
      rw [write_zero, freeM_pure_bind]
      rfl
    · obtain ⟨left, hl, _⟩ := hc.leftRead (by simp [hop])
      simp only [execution, hop, SailRV32.Functions.execute_ITYPE, hz,
        freeM_bind_assoc, freeM_pure_bind]
      rw [run_bind_of_ok _ _ _ _ _ hl, write_zero, freeM_pure_bind]
      rfl
    · obtain ⟨left, hl, _⟩ := hc.leftRead (by simp [hop])
      obtain ⟨right, hr, _⟩ := hc.rightRead (by simp [hop])
      simp only [execution, hop, SailRV32.Functions.execute_RTYPE, hz,
        freeM_bind_assoc, freeM_pure_bind]
      rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr]
      rw [write_zero, freeM_pure_bind]
      rfl
    · simp only [execution, hop, SailRV32.Functions.execute_UTYPE, hz,
        freeM_pure_bind, write_zero]
      rfl
    · have hp := hc.pcRead
      simp only [execution, hop, SailRV32.Functions.execute_UTYPE, hz,
        freeM_bind_assoc, freeM_pure_bind]
      rw [run_bind_of_ok _ _ _ _ _ hp, write_zero, freeM_pure_bind]
      rfl
  refine ⟨input.before, executed, ?_⟩
  rw [writeResult, hz, write_zero, freeM_pure_bind]
  rfl

/-- Connect a proved result equation to the actual generated execution clauses.
    This lemma introduces no separate instruction-specification relation. -/
theorem spec_of_result {input : Input} {output : Word} (hc : Contract input)
    (nonzero : input.rd ≠ zeroRegister)
    (h : output.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec) :
    destinationSpec input output := by
  have leftRead (condition : input.row.opcode = .add ∨ input.row.opcode = .addi ∨ input.row.opcode = .sub) :
      run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.row.left.toBitVec input.before := by
    obtain ⟨value, read, mapping⟩ := hc.leftRead condition
    simpa only [mapping nonzero] using read
  have rightRead (condition : input.row.opcode = .add ∨ input.row.opcode = .sub) :
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.row.right.toBitVec input.before := by
    obtain ⟨value, read, mapping⟩ := hc.rightRead condition
    simpa only [mapping nonzero] using read
  have pcRead (_condition : input.row.opcode = .auipc) :
      run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.row.pc.toBitVec input.before := by
    exact hc.pcRead
  have he : run (execution input) input.before = run (writeResult input.rd output) input.before := by
    unfold execution writeResult
    cases hop : input.row.opcode
    · simp only [hop, SailRV32.Functions.execute_RTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (leftRead (by simp [hop]))]
      rw [run_bind_of_ok _ _ _ _ _ (rightRead (by simp [hop]))]
      rw [← h]
    · simp only [hop, SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (leftRead (by simp [hop]))]
      rw [← hc.signExtension nonzero hop, ← h]
    · simp only [hop, SailRV32.Functions.execute_RTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (leftRead (by simp [hop]))]
      rw [run_bind_of_ok _ _ _ _ _ (rightRead (by simp [hop]))]
      rw [← h]
    · simp only [hop, SailRV32.Functions.execute_UTYPE, freeM_pure_bind] at h ⊢
      rw [← hc.upperImmediate nonzero (by simp [hop]), ← h]
    · simp only [hop, SailRV32.Functions.execute_UTYPE, freeM_bind_assoc, freeM_pure_bind] at h ⊢
      rw [run_bind_of_ok _ _ _ _ _ (pcRead hop)]
      rw [← hc.upperImmediate nonzero (by simp [hop]), ← h]
  obtain ⟨after, hw⟩ := write_success input.rd output.toBitVec input.before
  have hw' : run (writeResult input.rd output) input.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold writeResult
    rw [run_bind_of_ok _ _ _ _ _ hw]
    rfl
  exact ⟨after, he.trans hw', hw'⟩

/-- Sail's actual integer truncation is native word construction for naturals. -/
theorem truncate_nat (width n : Nat) :
    SailRV32.Functions.to_bits_truncate (l := width) (n : Int) = BitVec.ofNat width n := by
  apply BitVec.eq_of_toNat_eq
  simp [SailRV32.Functions.to_bits_truncate, _root_.Sail.get_slice_int, Nat.pow_succ]

end Airbender.Reference.RiscV.Sail
