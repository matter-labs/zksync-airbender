import Airbender.Proofs.JumpBranchSlt.PortReads
import Tests.Jump

namespace Tests.JumpPorts
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

-- The source and destination are both x1. Its old value is five, whereas
-- the link written by JALR is four. Native memory must retain that old read.
private def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 28 then 5 else Tests.Jump.row true false false i

private def entry : JumpBranchSlt.ProgramEntry :=
  ⟨0, 0xffc080e7, .JALR (0xffc, .Regidx 1, .Regidx 1),
    ⟨(), 1, 0, 1, ⟨65532, 65535⟩, 2, 0⟩⟩

private def before : State :=
  wordWriteState { (default : State) with regs :=
    Std.ExtDHashMap.emptyWithCapacity.insert .x1 (5 : BitVec 32) } 0 entry.bits

private theorem constraints :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
      JumpBranchSlt.importedConstraints := by
  simpa [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Lookup.Contains,
    Expression.eval, Verification.environment, assignment, Vector.map, Verification.range16,
    Verification.pairLookup,
    Verification.jumpCleanup] using
      Tests.Jump.satisfies true false false

private theorem query : JumpBranchSlt.decoderQuery assignment = entry.query := by decide

private theorem image : JumpBranchSlt.programImage before [0] = some [entry] := by
  have bytes : (Cell.ram 0).read before = .ok entry.bits before :=
    written_word_read _ 0 entry.bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind]
  rfl

/-- The history is built from actual native Sail reads/writes, including the
    old destination value; no post-write value is substituted for the source. -/
private theorem history : ∃ after,
    SailHistory [.register 0, .register 1]
      (JumpBranchSlt.Proofs.nativeEvents 1 assignment).reverse before after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) after = .ok 4 after := by
  have left : (Cell.register 1).read before = .ok 5 before := by
    apply read_register
    simp [before, wordWriteState]
  obtain ⟨after, written, _, readback⟩ := gpr_write_readback 1 4 before (by intro h; cases h)
  refine ⟨after, ?_, readback⟩
  have events : (JumpBranchSlt.Proofs.nativeEvents 1 assignment).reverse =
      [(3, (Cell.register 1).addressCode, Nat.pair 5 0, Nat.pair 4 0),
       (2, (Cell.register 0).addressCode, Nat.pair 0 0, Nat.pair 0 0),
       (1, (Cell.register 1).addressCode, Nat.pair 5 0, Nat.pair 5 0) ] := by
    norm_num [JumpBranchSlt.Proofs.nativeEvents, Trace.nativeRowEvents,
      JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns,
      MemoryPort.event, MemoryAddress.code, Cell.addressCode, MemoryPort.readCode,
      MemoryPort.writeCode, pairCode, decodeTimestamp, Timestamp.value, assignment,
      Tests.Jump.row, ZMod.val_ofNat, ZMod.val_one, babyBearModulus]
    rfl
  rw [events]
  have five : memoryWord (Nat.pair 5 0) = (5 : BitVec 32) := by
    simp [memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value]
  have four : memoryWord (Nat.pair 4 0) = (4 : BitVec 32) := by
    simp [memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value]
  refine .cons (.cons (.cons (.nil before) (.register 1) (by simp) rfl
    (by simpa only [five] using left)
    (by simpa only [five] using Proofs.cell_write_same left)) (.register 0) (by simp)
    rfl (by rfl) (by rfl)) (.register 1) (by simp) rfl
    (by simpa only [five] using left) (by simpa only [four, Cell.write] using written)

/-- Public Sail decoding and the full imported constraints bind the aliased row. -/
theorem accepted_alias_fetched : JumpBranchSlt.Fetched assignment before := by
  apply JumpBranchSlt.fetched (by decide) image constraints
  change ∃ i, _
  exact ⟨⟨0, by decide⟩, query⟩

/-- The reused port proof reads the old x1=5 and writes the link x1=4. -/
theorem aliased_register_effects : ∃ after,
    SailHistory [.register 0, .register 1]
      (JumpBranchSlt.Proofs.nativeEvents 1 assignment).reverse before after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) before = .ok 5 before ∧
    run (SailRV32.Functions.wX_bits (.Regidx 1) 4) before = .ok () after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) after = .ok 4 after := by
  obtain ⟨after, history, readback⟩ := history
  have reads := JumpBranchSlt.Proofs.register_reads (by decide) 1 query history
  have written := JumpBranchSlt.Proofs.register_write (by decide) 1 query history
  have source : memoryWord (JumpBranchSlt.importedConstraintsMemoryPorts[(0 : Fin 3)].readCode assignment) =
      (5 : BitVec 32) := by
    norm_num [memoryWord, JumpBranchSlt.importedConstraintsMemoryPorts,
      MemoryPort.readCode, pairCode, assignment, Tests.Jump.row,
      ZMod.val_ofNat, babyBearModulus, Word.toBitVec, Word.value]
    rfl
  have result : memoryWord (JumpBranchSlt.importedConstraintsMemoryPorts[2].writeCode assignment) =
      (4 : BitVec 32) := by
    norm_num [memoryWord, JumpBranchSlt.importedConstraintsMemoryPorts,
      MemoryPort.writeCode, pairCode, assignment, Tests.Jump.row,
      ZMod.val_ofNat, babyBearModulus, Word.toBitVec, Word.value]
    rfl
  refine ⟨after, history, ?_, ?_, readback⟩
  · have read := reads 0
    rw [source] at read
    exact read
  · rw [result] at written
    exact written

/-- An invented old rd value cannot represent this public pre-state, even when
    the same source/destination register aliases and the decoder query is valid. -/
theorem wrong_old_destination_rejected :
    ¬ ∃ after, SailHistory [.register 0, .register 1]
      (JumpBranchSlt.Proofs.nativeEvents 1
        (fun i => if i = 28 then 0 else assignment i)).reverse before after := by
  rintro ⟨after, history⟩
  have query : JumpBranchSlt.decoderQuery (fun i => if i = 28 then 0 else assignment i) =
      entry.query := by decide
  have read := JumpBranchSlt.Proofs.register_reads (by decide) 1 query history 2
  have zero : memoryWord (JumpBranchSlt.importedConstraintsMemoryPorts[(2 : Fin 3)].readCode
      (fun i => if i = 28 then 0 else assignment i)) = (0 : BitVec 32) := by
    norm_num [memoryWord, JumpBranchSlt.importedConstraintsMemoryPorts,
      MemoryPort.readCode, pairCode, assignment, Tests.Jump.row,
      ZMod.val_ofNat, babyBearModulus, Word.toBitVec, Word.value]
    rfl
  rw [zero] at read
  change run (SailRV32.Functions.rX_bits (.Regidx 1)) before = .ok (0 : BitVec 32) before at read
  have actual : run (SailRV32.Functions.rX_bits (.Regidx 1)) before = .ok (5 : BitVec 32) before := by
    apply read_register
    simp [before, wordWriteState]
  have impossible := (EStateM.Result.ok.inj (actual.symm.trans read)).1
  exact (by decide : (5 : BitVec 32) ≠ 0) impossible

end Tests.JumpPorts
