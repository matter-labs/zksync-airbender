import Airbender.Proofs.Sail.PC

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

variable [MemoryPlatform SailRV32.exception]

omit [MemoryPlatform SailRV32.exception] in
theorem extend_word (unsigned : Bool) (value : BitVec 32) :
    SailRV32.Functions.extend_value unsigned value = value := by
  cases unsigned <;> simp [SailRV32.Functions.extend_value,
    SailRV32.Functions.sign_extend, SailRV32.Functions.zero_extend,
    _root_.Sail.BitVec.signExtend, _root_.Sail.BitVec.zeroExtend]

/-- The original LW clause, after a successful native memory access. -/
theorem load_word {before : State} {imm : BitVec 12} {rs1 rd : SailRV32.regidx}
    {value : BitVec 32}
    (read : run (SailRV32.Functions.vmem_read rs1
      (SailRV32.Functions.sign_extend (m := 32) imm) 4 (.Load .Data) false false false) before =
        .ok (.Ok value) before) :
    run (SailRV32.Functions.execute_LOAD imm rs1 rd false 4) before =
      run (do SailRV32.Functions.wX_bits rd value; pure SailRV32.Functions.RETIRE_SUCCESS) before := by
  have width : decide (4 ≤ SailRV32.Functions.xlen_bytes) = true := by decide
  have assertion (message : String) : SailRV32.assert true message = (pure () : SailRV32.SailM Unit) := rfl
  simp only [SailRV32.Functions.execute_LOAD, width]
  rw [assertion, freeM_pure_bind, run_bind_of_ok _ _ _ _ _ read]
  simp only [extend_word]

/-- The original SW clause reads rs2 and performs a native memory access. -/
theorem store_word {before after : State} {imm : BitVec 12} {rs1 rs2 : SailRV32.regidx}
    {value : BitVec 32}
    (read : run (SailRV32.Functions.rX_bits rs2) before = .ok value before)
    (write : run (SailRV32.Functions.vmem_write rs1
      (SailRV32.Functions.sign_extend (m := 32) imm) 4 value (.Store .Data) false false false) before =
        .ok (.Ok true) after) :
    run (SailRV32.Functions.execute_STORE imm rs2 rs1 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  change run (SailRV32.Functions.rX_bits rs2 >>= fun data =>
    SailRV32.Functions.vmem_write rs1 (SailRV32.Functions.sign_extend (m := 32) imm) 4
      (_root_.Sail.BitVec.extractLsb data 31 0) (.Store .Data) false false false >>= fun result =>
      match result with
      | .Ok _ => pure SailRV32.Functions.RETIRE_SUCCESS
      | .Err error => pure error) before = _
  rw [run_bind_of_ok _ _ _ _ _ read]
  have extract (v : BitVec 32) : _root_.Sail.BitVec.extractLsb v 31 0 = v := by
    simp [_root_.Sail.BitVec.extractLsb, BitVec.extractLsb]
  simp only [extract]
  rw [run_bind_of_ok _ _ _ _ _ write]
  rfl

omit [MemoryPlatform SailRV32.exception] in
/-- The runtime, rather than a local memory model, implements the four-byte write.
    It succeeds and leaves all architectural registers unchanged. -/
theorem write_word_frame (address : BitVec 32) (value : BitVec 32) (before : State) :
    ∃ after, run (writeMemory (size := 4) address value) before = .ok () after ∧
      after.regs = before.regs := by
  exact ⟨_, rfl, rfl⟩

end Airbender.Reference.RiscV.Sail
