import Tests.JumpSailHistory
import Slop.JumpBranchSlt.Claims
import Slop.JumpBranchSlt.Execution
import Slop.JumpBranchSlt.Composition

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
      initialState (retiredState before 0) (4, 0) = some (trace rom).initial ∧
      run (normalStep (SailRV32.Functions.execute_JALR 0xffc (.Regidx 1) (.Regidx 1)))
        (retiredState before 0) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after 0) ∧
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
  have native : SailHistory cells
      (JumpBranchSlt.Proofs.nativeEvents (trace rom).memoryEpoch assignment).reverse before after := by
    simpa [Trace.rowEvents, row, Row.ports, Row.columns] using execution
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
  have code : memoryWord (JumpBranchSlt.importedConstraintsMemoryPorts[2].writeCode assignment) =
      (4 : BitVec 32) := by
    norm_num [memoryWord, JumpBranchSlt.importedConstraintsMemoryPorts,
      MemoryPort.writeCode, pairCode, assignment, JumpHistory.assignment,
      JumpTimestamp.assignment, Word.toBitVec, Word.value, ZMod.val_ofNat, babyBearModulus]
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
theorem actual_jalr_trace
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

private def pooledProgram  : List PooledProgramEntry :=
  [entry.mapFamily (fun _ => .jumpBranchSlt)]

private def pooled  : PooledTrace babyBearModulus where
  rows := [⟨.jumpBranchSlt, row.assignment⟩]
  rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words before)⟩
  initial := (trace (ROM.table cells seed)).initial
  terminal := (trace (ROM.table cells seed)).terminal
  initialMemory := seed
  terminalMemory := (trace (ROM.table cells seed)).terminalMemory

private theorem pooledAccepted  : Accepted (pooled) := by
  constructor
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    exact constraints
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    rfl
  · exact (accepted (ROM.table cells seed)).states
  · exact (accepted (ROM.table cells seed)).memory

private theorem pooledImage  :
    pooledProgramImage before [0] = some (pooledProgram) := by
  have source := Proofs.program_sources (program_image) entry (by simp)
  have bytes := source.bytes
  change (Cell.ram 0).read before = .ok entry.bits before at bytes
  simp only [pooledProgramImage, programImageWith, List.mapM_cons, List.mapM_nil,
    programEntryWith, bytes, source.decoded, bind, Option.bind]
  rfl

private theorem pooledDecoded  : PooledDecoded (pooled) (pooledProgram) := by
  intro actual member
  simp only [pooled, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _ = _
  exact ⟨0, by decide⟩

private theorem pooledInputs  :
    NativeInputs pooledDecoderFields (pooled) before cells (pooledProgram) := by
  refine ⟨by decide, ?_, image, ?_, ⟨[0], pooledImage⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · refine ⟨(4, 0), ?_⟩
    have read : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
      apply read_register
      simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    rw [initialState, read]
    rfl
  · exact ⟨(boundary (ROM.table cells seed)).initial,
      (boundary (ROM.table cells seed)).aligned,
      (boundary (ROM.table cells seed)).memory⟩

private theorem sharedInputs  :
    JumpBranchSlt.TraceInputs (pooled) before cells (pooledProgram) := by
  refine ⟨⟨pooledInputs, rfl, rfl⟩, ?_, ?_⟩
  · intro actual member
    simp only [pooledProgram, List.mem_singleton] at member
    subst actual
    decide
  · constructor <;> decide

theorem per_circuit_jalr_soundness  :
    ∃ input : JumpBranchSlt.Jump.Input,
      (JumpBranchSlt.Jump.circuitModel (pooled) before cells (pooledProgram)).relation
        input (⟨⟨4, 0⟩, ⟨0, 0⟩⟩ : Output) (row.assignment) ∧
      JumpBranchSlt.Jump.InterfaceAssumptions (pooled) before cells (pooledProgram)
        input (⟨⟨4, 0⟩, ⟨0, 0⟩⟩ : Output) (row.assignment) ∧
      JumpBranchSlt.Jump.spec input (⟨⟨4, 0⟩, ⟨0, 0⟩⟩ : Output) := by
  have member : (⟨.jumpBranchSlt, row.assignment⟩ : Row babyBearModulus PooledFamily) ∈
      (pooled).rows := by simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    (pooledAccepted) (pooledInputs).clocks (pooledInputs).image
    (pooledInputs).distinct (pooledInputs).aligned
    (pooledImage) (pooledDecoded) member
  let input : JumpBranchSlt.Jump.Input := ⟨.jalr 0xffc, ⟨5, 0⟩, ⟨65532, 65535⟩, ⟨0, 0⟩, .Regidx 1, .Regidx 1, current⟩
  let output : Output := ⟨⟨4, 0⟩, ⟨0, 0⟩⟩
  have mapping : JumpBranchSlt.Jump.TraceMapping (pooled) before cells
      (pooledProgram) input output (row.assignment) := by
    refine ⟨?_, position, ?_⟩
    · constructor <;> first | rfl | (intro _; rfl)
    · refine ⟨entry.mapFamily (fun _ => .jumpBranchSlt), by simp [pooledProgram], rfl, ?_, ?_⟩
      · decide
      · rfl
  have assumptions : JumpBranchSlt.Jump.InterfaceAssumptions (pooled) before cells
      (pooledProgram) input output (row.assignment) := {
    toTraceInputs := sharedInputs
    isa := by refine ⟨0, ?_⟩; simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    landingPad := by
      intro _
      refine ⟨?_, 0, ?_, by decide⟩
      · simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
      · simp [before, wordWriteState]
  }
  have core := Verification.holds_of_sublist (constraints)
    (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
  have relation : (JumpBranchSlt.Jump.circuitModel (pooled) before cells
      (pooledProgram)).relation input output (row.assignment) :=
    ⟨⟨pooledAccepted, pooledDecoded, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, JumpBranchSlt.Jump.babyBear_soundness (pooled)
    before cells (pooledProgram) input output _ ⟨assumptions, relation⟩⟩

theorem per_circuit_pc_alias_rejected (current : State) :
    ¬ JumpBranchSlt.Jump.TraceMapping pooled before cells pooledProgram
      (⟨.jalr 0xffc, ⟨5, 0⟩, ⟨65532, 65535⟩, ⟨babyBearModulus, 0⟩,
        .Regidx 1, .Regidx 1, current⟩ : JumpBranchSlt.Jump.Input)
      ⟨⟨4, 0⟩, ⟨0, 0⟩⟩ row.assignment := by
  intro mapping
  have impossible := mapping.words.pcLo
  change babyBearModulus = (row.assignment 0).val at impossible
  have small := ZMod.val_lt (row.assignment 0)
  omega

end Tests.JalrTrace
