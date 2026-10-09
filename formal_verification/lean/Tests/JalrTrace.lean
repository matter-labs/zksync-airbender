import Tests.JumpSailHistory
import Airbender.Proofs.JumpBranchSlt.Execution
import Airbender.Proofs.JumpBranchSlt.Composition

namespace Tests.JalrTrace
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

-- JALR x1,-4(x1): the old source is five, the link is four, and target is zero.
private def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 5 then 1 else if i = 11 then 0 else if i = 12 then 1
  else if i = 16 || i = 17 || i = 24 then 0
  else if i = 22 then 5 else if i = 32 then 4
  else if i = 36 || i = 39 || i = 40 then 1
  else JumpHistory.assignment 5 false i

private def entry : JumpBranchSlt.ProgramEntry :=
  ⟨0, 0xffc080e7, .JALR (0xffc, .Regidx 1, .Regidx 1),
    ⟨(), 1, 0, 1, ⟨65532, 65535⟩, 2, 0⟩⟩

private def before : State :=
  wordWriteState { (default : State) with regs :=
    ((Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (5 : BitVec 32) |>.insert .PC 0
      |>.insert .misa (0 : BitVec 32) |>.insert .cur_privilege .Machine
      |>.insert .mseccfg (0 : BitVec 64)) } 0 entry.bits

private def cells : List Cell := [.register 0, .register 1]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 5]
private def row : Row babyBearModulus JumpBranchSlt.TraceKind := ⟨.jumpBranchSlt, assignment⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), Nat.pair 0 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 4 0⟩]

private theorem constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) JumpBranchSlt.clockConstraints := by
  apply Verification.holds_append (left := JumpBranchSlt.importedConstraints)
    (right := JumpBranchSlt.importedConstraintsTimestampLookups)
  · simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, assignment,
      JumpHistory.assignment, JumpTimestamp.assignment]
    repeat' apply And.intro
    all_goals first
      | decide
      | (apply Verification.range16_contains; decide)
      | (with_unfolding_all change ∃ i : Fin 65536,
          ((0, 0) : fieldPair (ZMod babyBearModulus)) =
            ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
         exact ⟨0, rfl⟩)
      | (with_unfolding_all change ∃ i : Fin 131072,
          ((4, 0) : fieldPair (ZMod babyBearModulus)) =
            ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
         exact ⟨4, rfl⟩)
      | (with_unfolding_all change ∃ i : Fin 4194304,
          ((0, 0) : fieldPair (ZMod babyBearModulus)) =
            ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
         exact ⟨0, rfl⟩)
      | (with_unfolding_all change ∃ i : Fin 65536,
          ((1, 0, 0) : fieldTriple (ZMod babyBearModulus)) =
            ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus),
              ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
         exact ⟨1, rfl⟩)
  · simp [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment,
      JumpHistory.assignment, JumpTimestamp.assignment]
    all_goals decide

private theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) : Accepted (trace rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact constraints
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
      JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns]
    decide

private theorem boundary (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace rom) := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

private theorem image : initialImage before cells = some seed := by
  have zero : (Cell.register 0).read before = .ok 0 before := rfl
  have one : (Cell.register 1).read before = .ok 5 before := by
    apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, zero, one]
  rfl

private theorem program_image : JumpBranchSlt.programImage before [0] = some [entry] := by
  have bytes : (Cell.ram 0).read before = .ok entry.bits before := written_word_read _ 0 entry.bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind]
  rfl

private theorem query : JumpBranchSlt.decoderQuery assignment = entry.query := by decide

private theorem decoded (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.Decoded (trace rom) [entry] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i, _
  exact ⟨⟨0, by decide⟩, query⟩

/-- Full native matching and public Sail images derive the aliased cell history;
    the original JALR clause then reaches its actual native retired after-state. -/
theorem actual_jalr_retirement (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      initialState (Proofs.retiredState before 0) (4, 0) = some (trace rom).initial ∧
      run (normalStep (SailRV32.Functions.execute_JALR 0xffc (.Regidx 1) (.Regidx 1)))
        (Proofs.retiredState before 0) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (Proofs.retiredState after 0) ∧
      run (SailRV32.Functions.rX_bits (.Regidx 1)) after = .ok 4 after ∧
      after.regs.get? .misa = before.regs.get? .misa ∧
      after.regs.get? .cur_privilege = before.regs.get? .cur_privilege ∧
      after.regs.get? .mseccfg = before.regs.get? .mseccfg := by
  obtain ⟨history, rows, after, _, permutation, _, execution, _⟩ :=
    JumpBranchSlt.Proofs.decoded_native_history (by decide) (by decide)
      (accepted rom) (boundary rom) image (by decide)
      (by intro cell member; simp [cells] at member; rcases member with rfl | rfl <;> trivial)
      program_image (decoded rom)
  have single : rows = [row] := by simpa only [trace] using List.perm_singleton.mp permutation
  subst rows
  have native : Proofs.SailHistory cells
      (JumpBranchSlt.Proofs.nativeEvents (trace rom).memoryEpoch assignment).reverse before after := by
    simpa [Proofs.rowEvents, row, Row.ports, Row.columns] using execution
  have checked := JumpBranchSlt.Proofs.jump_rebased_step (by decide) (by decide)
    (accepted rom) (boundary rom) image program_image (decoded rom)
    (by change (⟨0, 0⟩ : Word).Bounded; constructor <;> decide)
    (by change 0 % 4 = 0; decide)
    (by simp [trace, row]) (by simp) query (.jalr 0xffc) 1 1 rfl native (.nil before)
    (by refine ⟨0, ?_⟩; simp [before, wordWriteState, Std.ExtDHashMap.get?_insert])
    (by intro _
        refine ⟨?_, 0, ?_, by decide⟩
        · simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
        · simp [before, wordWriteState])
  have written := JumpBranchSlt.Proofs.register_write (by decide) (trace rom).memoryEpoch query native
  have code : Proofs.memoryWord (JumpBranchSlt.importedConstraintsMemoryPorts[2].writeCode assignment) =
      (4 : BitVec 32) := by
    norm_num [Proofs.memoryWord, JumpBranchSlt.importedConstraintsMemoryPorts,
      MemoryPort.writeCode, pairCode, assignment, JumpHistory.assignment,
      JumpTimestamp.assignment, Word.toBitVec, Word.value, ZMod.val_ofNat, babyBearModulus]
    rfl
  rw [code] at written
  change run (SailRV32.Functions.wX_bits (.Regidx 1) 4) before = .ok () after at written
  obtain ⟨actual, write, _, read⟩ := gpr_write_readback 1 4 before (by intro h; cases h)
  have same := (EStateM.Result.ok.inj (written.symm.trans write)).2
  subst actual
  refine ⟨after, ?_, checked, read, Proofs.sail_history_control_flow_csrs native⟩
  rw [initialState, Proofs.retired_state_pc before 0]
  rfl

/-- The whole-trace theorem starts at the unmodified public Sail state,
    derives the actual aliased JALR clause, and reaches the native terminal PC. -/
theorem actual_jalr_trace [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after, JumpBranchSlt.SailTrace [entry] before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 0 after := by
  have initialPC : initialState before (4, 0) = some (trace rom).initial := by
    have read : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
      apply read_register
      simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    rw [initialState, read]
    rfl
  have inputs : JumpBranchSlt.ExecutionBoundary (trace rom) before cells [entry] := {
    distinct := by decide
    aligned := by intro cell member; simp [cells] at member; rcases member with rfl | rfl <;> trivial
    image := image
    initialPC := ⟨(4, 0), initialPC⟩
    initialAligned := by change 0 % 4 = 0; decide
    terminalCanonical := by change (⟨0, 0⟩ : Word).Bounded; constructor <;> decide
    programImage := ⟨[0], program_image⟩
    clocks := boundary rom
    misa := by refine ⟨0, ?_⟩; simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    indirect := by
      refine ⟨?_, 0, ?_, by decide⟩
      · simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
      · simp [before, wordWriteState]
  }
  obtain ⟨after, execution, pc, _⟩ := JumpBranchSlt.Proofs.native_trace_execution
    (by decide) (by decide) inputs (accepted rom) (decoded rom)
  exact ⟨after, execution, pc⟩

end Tests.JalrTrace
