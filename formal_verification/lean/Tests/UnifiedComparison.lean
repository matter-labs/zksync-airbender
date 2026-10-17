import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Proofs.BabyBear
import Airbender.Review.Trace.UnifiedReduced.Theorems
import Airbender.Proofs.Sail.WordMemoryState

set_option Elab.async false

namespace Tests.UnifiedComparison
open Airbender Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
open Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

private def assignment (immediate : Bool) : Nat → ZMod babyBearModulus
  | 4 | 7 | 23 | 44 | 84 | 88 | 130 | 131 | 132 | 133 => 1
  | 2 | 30 | 40 | 81 | 120 | 122 => 4
  | 8 | 9 | 60 | 102 => if immediate then 65535 else 0
  | 10 => 3
  | 32 => 8
  | 50 | 52 | 53 | 59 | 61 | 78 | 89 | 103 | 112 => if immediate then 1 else 0
  | 57 | 90 => if immediate then 0 else 1
  | 92 | 101 => 5
  | 110 => 51
  | 111 => if immediate then 53 else 56
  | 119 => 2
  | _ => 0

private def row (immediate : Bool) : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment immediate⟩
private def cells : List Cell := [.register 0, .register 1]
private def before (immediate : Bool) : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .PC 0 |>.insert .misa 0x40000100 |>.insert .x1 0
    mem := (Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 (if immediate then 0x93 else 0xb3) |>.insert 1 0x30
      |>.insert 2 (if immediate then 0xf0 else 0) |>.insert 3 (if immediate then 0xff else 0) }
private def trace (immediate : Bool) : UnifiedTrace babyBearModulus where
  rows := [row immediate]
  rom := UnifiedReduced.Setup.table (before immediate)
  initial := (row immediate).start
  terminal := (row immediate).finish
  initialMemory := cells.map fun cell => cell.initialToken 0
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), Nat.pair 0 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair (if immediate then 1 else 0) 0⟩]
private def entry (immediate : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, if immediate then 0xfff03093 else 0x000030b3,
    if immediate then .ITYPE (4095, .Regidx 0, .Regidx 1, .SLTIU)
    else .RTYPE (.Regidx 0, .Regidx 0, .Regidx 1, .SLTU),
    ⟨.machine, 0, 0, 1, ⟨if immediate then 65535 else 0, if immediate then 65535 else 0⟩, 4096, 3⟩⟩

private theorem constraints (immediate : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment immediate)) (UnifiedReduced.clockConstraints (trace immediate).rom) := by
  apply Verification.holds_append
  · cases immediate <;> simp [UnifiedReduced.importedConstraints, trace,
      FlatOperation.ConstraintsHoldFlat, Verification.environment, Expression.eval, assignment,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (with_unfolding_all refine ⟨⟨524545, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
      | (with_unfolding_all refine ⟨⟨524546, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
      | (with_unfolding_all refine ⟨⟨655617, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
      | (with_unfolding_all refine ⟨⟨786742, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
          UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
      | (with_unfolding_all refine ⟨⟨786745, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
          UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
      | (with_unfolding_all refine ⟨⟨721157, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
      | (with_unfolding_all refine ⟨⟨721152, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
  · cases immediate <;> simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private theorem accepted (immediate : Bool) : Accepted (trace immediate) := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact constraints immediate
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · cases immediate <;> decide

private theorem public_image (immediate : Bool) :
    initialImage (before immediate) cells = some (trace immediate).initialMemory := by
  have x0 : (Cell.register 0).read (before immediate) = .ok 0 (before immediate) := rfl
  have x1 : (Cell.register 1).read (before immediate) = .ok 0 (before immediate) := by
    apply read_register
    simp [before]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x0, x1, bind, Option.bind]
  rfl

private theorem program_image (immediate : Bool) :
    UnifiedReduced.programImage (before immediate) [0] = some [entry immediate] := by
  have bytes : (Cell.ram 0).read (before immediate) = .ok (entry immediate).bits (before immediate) := by
    cases immediate <;> simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, entry, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, bind, Option.bind, pure]
  cases immediate <;> with_unfolding_all rfl

private theorem inputs (immediate : Bool) :
    NativeInputs UnifiedReduced.decoderFields (trace immediate) (before immediate) cells [entry immediate] := by
  refine ⟨by decide, ?_, public_image immediate, ⟨⟨4, 0⟩, ?_⟩, ⟨[0], program_image immediate⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · have pc : run (SailRV32.Functions.get_arch_pc ()) (before immediate) = .ok 0 (before immediate) := by
      apply read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    simp [initialState, pc, trace, row, Row.start, Row.columns, CircuitLayout.columns,
      UnifiedReduced.importedConstraintsTraceColumns, rawPair, assignment, PCState.boundary, PCState.encode, limbBase]
  · constructor
    · cases immediate <;> constructor <;> decide
    · cases immediate <;> decide
    · intro token member
      cases immediate <;> simp [trace, cells, Cell.initialToken] at member
      all_goals rcases member with rfl | rfl
      all_goals constructor <;> decide

private theorem decoded (immediate : Bool) : UnifiedReduced.Decoded (trace immediate) [entry immediate] := by
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  change ∃ i : Fin 1, _
  exact ⟨0, by cases immediate <;> decide⟩

private def input (immediate : Bool) : UnifiedReduced.Control.Comparison.Input :=
  ⟨if immediate then .sltiu else .sltu, ⟨0, 0⟩,
    ⟨if immediate then 65535 else 0, if immediate then 65535 else 0⟩, ⟨0, 0⟩,
    .Regidx 0, .Regidx 0, .Regidx 1, if immediate then 4095 else 0,
    Trace.retiredState (before immediate) 0⟩
private def output (immediate : Bool) : Output := ⟨⟨if immediate then 1 else 0, 0⟩, ⟨4, 0⟩⟩

theorem sail_comparisons (immediate : Bool) : JumpBranchSlt.Comparison.spec (input immediate) (output immediate) := by
  apply UnifiedReduced.Control.Comparison.soundness (by decide) (by decide) (trace immediate)
    (before immediate) cells [entry immediate] (input immediate) (output immediate) (assignment immediate)
  refine ⟨⟨inputs immediate, rfl, ?_⟩,
    ⟨accepted immediate, decoded immediate, by simp [trace, row]⟩, ?_⟩
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    change (0 : Nat) % 4 = 0
    decide
  · constructor
    · cases immediate <;> constructor
      all_goals rfl
    · exact ⟨[], [], before immediate, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
    · exact ⟨entry immediate, by simp, by cases immediate <;> decide, by cases immediate <;> rfl⟩

private def wrappedInitial : State :=
  { (before true) with regs := ((before true).regs.insert .x12 (65537 : BitVec 32)).insert .PC (0xfffffffc : BitVec 32) }
private def wrappedBefore : State :=
  wordWriteState (wordWriteState wrappedInitial 0xfffffffc 0xfff03613) 0 0x00000613
private def wrappedCompareAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 0 then 65532 else if column = 1 then 65535
  else if column = 7 || column = 44 then 12
  else if column = 30 || column = 81 || column = 120 || column = 122 then 0
  else if column = 48 || column = 49 || column = 54 || column = 55 then 1
  else assignment true column
private def wrappedResetAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 || column = 40 then 8
  else if column = 30 then 4 else if column = 32 then 12
  else if column = 34 then 5 else if column = 46 then 6
  else if column = 7 || column = 44 then 12
  else if column = 4 || column = 11 || column = 48 || column = 129 || column = 130 ||
      column = 131 || column = 132 || column = 133 then 1
  else 0
private def wrappedCompareRow : Row babyBearModulus UnifiedFamily := ⟨.machine, wrappedCompareAssignment⟩
private def wrappedResetRow : Row babyBearModulus UnifiedFamily := ⟨.machine, wrappedResetAssignment⟩
private def wrappedCompareEntry : UnifiedReduced.ProgramEntry :=
  ⟨0xfffffffc, 0xfff03613, .ITYPE (4095, .Regidx 0, .Regidx 12, .SLTIU),
    ⟨.machine, 0, 0, 12, ⟨65535, 65535⟩, 4096, 3⟩⟩
private def wrappedResetEntry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0x00000613, (UnifiedReduced.Caller.ControlLiteral.addi 0).instruction 12,
    ⟨.machine, 0, 0, 12, ⟨0, 0⟩, 1, 0⟩⟩
private def wrappedProgram : List UnifiedReduced.ProgramEntry := [wrappedCompareEntry, wrappedResetEntry]
private def wrappedCells : List Cell := [.register 0, .register 12]
private def wrappedData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [wrappedResetRow, wrappedCompareRow]
    rom := UnifiedReduced.Setup.table wrappedBefore
    initial := wrappedCompareRow.start
    terminal := wrappedResetRow.finish
    initialMemory := [⟨(Cell.register 0).addressCode, (0, 0), 0⟩,
      ⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 1 1⟩]
    terminalMemory := [⟨(Cell.register 0).addressCode, (9, 0), 0⟩,
      ⟨(Cell.register 12).addressCode, (10, 0), 0⟩] }
  workers := ⟨Delegation.modeledSetup Keccak.Controller.rows, [], [], []⟩
  program := []

private theorem wrappedCore (reset : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (if reset then wrappedResetAssignment else wrappedCompareAssignment))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table wrappedBefore)) := by
  cases reset
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, wrappedCompareAssignment, wrappedResetAssignment, assignment,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
    | (with_unfolding_all refine ⟨⟨524545, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
    | (with_unfolding_all refine ⟨⟨524546, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
    | (with_unfolding_all refine ⟨⟨655617, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
    | (with_unfolding_all refine ⟨⟨721152, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
    | (with_unfolding_all refine ⟨⟨786742, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (with_unfolding_all refine ⟨⟨721153, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])

private theorem wrappedTimestamps (reset : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (if reset then wrappedResetAssignment else wrappedCompareAssignment))
    UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases reset <;> decide +kernel

private theorem wrappedAccepted : UnifiedReduced.Caller.MixedMemoryAccepted wrappedData wrappedProgram := by
  constructor
  · constructor
    · intro current member
      have rows : current = wrappedResetRow ∨ current = wrappedCompareRow := by simpa [wrappedData] using member
      rcases rows with rfl | rfl
      · exact Verification.holds_append (wrappedCore true) (wrappedTimestamps true)
      · exact Verification.holds_append (wrappedCore false) (wrappedTimestamps false)
    · intro current member
      have rows : current = wrappedResetRow ∨ current = wrappedCompareRow := by simpa [wrappedData] using member
      rcases rows with rfl | rfl <;> decide +kernel
    · change [wrappedCompareRow.start, wrappedResetRow.finish, wrappedCompareRow.finish].Perm
        [wrappedResetRow.finish, wrappedResetRow.start, wrappedCompareRow.start]
      have same : wrappedCompareRow.finish = wrappedResetRow.start := rfl
      rw [same]
      exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
    · intro current member
      have empty : wrappedData.callers = [] := by decide +kernel
      rw [empty] at member
      cases member
    · intro current member; cases member
    · intro current member; cases member
    · have empty : wrappedData.calls = [] := by decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = wrappedResetRow ∨ current = wrappedCompareRow := by simpa [wrappedData] using member
    rcases rows with rfl | rfl
    · change ∃ i : Fin 2, wrappedResetRow.decoderQuery = (wrappedProgram.get i).query
      exact ⟨1, by decide +kernel⟩
    · change ∃ i : Fin 2, wrappedCompareRow.decoderQuery = (wrappedProgram.get i).query
      exact ⟨0, by decide +kernel⟩
  · decide +kernel

private theorem wrappedImage : UnifiedReduced.Mixed.programImage wrappedBefore [0xfffffffc, 0] = some wrappedProgram := by
  have first : (Cell.ram 0xfffffffc).read wrappedBefore = .ok 0xfff03613 wrappedBefore :=
    written_word_disjoint 0 0x00000613 (by decide) (written_word_read wrappedInitial 0xfffffffc 0xfff03613)
  have second : (Cell.ram 0).read wrappedBefore = .ok 0x00000613 wrappedBefore :=
    written_word_read (wordWriteState wrappedInitial 0xfffffffc 0xfff03613) 0 0x00000613
  have decodeFirst : run (SailRV32.Functions.encdec_backwards 0xfff03613) wrappedBefore =
      .ok wrappedCompareEntry.instruction wrappedBefore := by with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards 0x00000613) wrappedBefore =
      .ok wrappedResetEntry.instruction wrappedBefore := by with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields wrappedCompareEntry.instruction = some wrappedCompareEntry.data := by
    with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields wrappedResetEntry.instruction = some wrappedResetEntry.data := by
    with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, decodeFirst, decodeSecond, fieldsFirst, fieldsSecond, bind, Option.bind, pure]
  rfl

private theorem wrappedInputs : UnifiedReduced.Caller.MixedMemoryInputs
    wrappedData wrappedProgram wrappedBefore [] [0xfffffffc, 0] wrappedCells := by
  refine ⟨⟨rfl, ?_, by decide +kernel⟩, wrappedImage, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · constructor <;> decide +kernel
  · have zero : (Cell.register 0).read wrappedBefore = .ok 0 wrappedBefore := by with_unfolding_all rfl
    have control : (Cell.register 12).read wrappedBefore = .ok 65537 wrappedBefore := by
      apply rX_register_frame (before := wrappedInitial) (after := wrappedBefore) rfl 12
      apply read_register
      simp [wrappedInitial, Std.ExtDHashMap.get?_insert]
    change initialImage wrappedBefore [.register 0, .register 12] = some wrappedData.machine.initialMemory
    simp only [initialImage, zero, control, List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 12 := by simpa [wrappedCells] using member
    rcases choices with rfl | rfl <;> trivial
  · intro current member; cases member

private theorem wrappedRegistry : UnifiedReduced.Caller.WrappedSequentialProgram wrappedProgram := by
  constructor
  · intro entry member
    have entries : entry = wrappedCompareEntry ∨ entry = wrappedResetEntry := by simpa [wrappedProgram] using member
    rcases entries with rfl | rfl
    · exact .sltiu 4095 0 12
    · exact .sequential (.arithmetic (.addi 0 0 12))
  · intro entry member
    have entries : entry = wrappedCompareEntry ∨ entry = wrappedResetEntry := by simpa [wrappedProgram] using member
    rcases entries with rfl | rfl <;> decide +kernel

private theorem wrappedPreparation : UnifiedReduced.Caller.ControlPreparation wrappedData wrappedProgram 12 12 (.addi 0) := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  apply UnifiedReduced.Caller.PreparationProgram.wrappedSequential (by decide +kernel) wrappedBefore rfl wrappedRegistry
  intro entry member atCut
  have entries : entry = wrappedCompareEntry ∨ entry = wrappedResetEntry := by simpa [wrappedProgram] using member
  rcases entries with rfl | rfl
  · have impossible : ¬ (wrappedCompareEntry.pc = wrappedData.machine.initial.word.toBitVec +
        BitVec.ofNat 32 (12 - 4 - (timeOfPair wrappedData.machine.initial.timestamp).value)) := by decide +kernel
    exact False.elim (impossible atCut)
  · rfl

theorem comparison_wrap_and_reset_accepted :
    UnifiedReduced.Caller.MixedMemoryAccepted wrappedData wrappedProgram ∧
    UnifiedReduced.Caller.MixedMemoryInputs wrappedData wrappedProgram wrappedBefore [] [0xfffffffc, 0] wrappedCells ∧
    wrappedCompareRow.start.word.toBitVec = 0xfffffffc ∧ wrappedCompareRow.finish.word.toBitVec = 0 :=
  ⟨wrappedAccepted, wrappedInputs, by decide +kernel, by decide +kernel⟩

theorem wrapped_preparation_derives_reset_control :
    UnifiedReduced.Caller.PreparedBoundaryExecution wrappedData wrappedBefore wrappedCells 12 12 (.addi 0) :=
  UnifiedReduced.Caller.control_preparation_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    wrappedAccepted wrappedInputs wrappedPreparation (by decide) (by decide)

theorem wrapped_native_addresses_derived :
    ∀ row ∈ wrappedData.machine.rows, row.start.word.toBitVec = wrappedData.machine.initial.word.toBitVec +
      BitVec.ofNat 32 (Delegation.Caller.startClock row - (timeOfPair wrappedData.machine.initial.timestamp).value) :=
  UnifiedReduced.Caller.wrapped_program_address_soundness (by decide +kernel) (by decide +kernel)
    rfl wrappedAccepted wrappedInputs.publicProgram wrappedInputs.ordinaryProgram wrappedRegistry

theorem wrapped_program_empty_region_at_pc_zero :
    UnifiedReduced.Caller.ProgramCallerWindow wrappedData .keccak 8 8 := by
  have region : UnifiedReduced.Caller.WrappedProgramCallerRegion wrappedData wrappedProgram .keccak 8 8 := by
    constructor
    · intro entry member clock lower upper; omega
    · intro entry member; cases member
  exact UnifiedReduced.Caller.wrapped_program_window_schedule_soundness (by decide +kernel) (by decide +kernel)
    rfl wrappedAccepted wrappedInputs.publicProgram wrappedInputs.ordinaryProgram wrappedRegistry region
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem wrapped_program_region_excludes_reset_at_zero :
    ¬ UnifiedReduced.Caller.WrappedProgramCallerRegion wrappedData wrappedProgram .keccak 8 12 := by
  intro region
  exact region.ordinary wrappedResetEntry (by simp [wrappedProgram]) 8
    (by decide) (by decide) (by decide +kernel)

theorem wrapped_preparation_uses_comparison_write :
    (readToken wrappedResetAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
    (readToken wrappedResetAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = 1 ∧
    (writeToken UnifiedReduced.importedConstraintsTraceColumns wrappedResetAssignment
      UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (10, 0) := by decide +kernel

theorem wrapped_prefix_and_preparation_share_history :
    ∃ chain : UnifiedReduced.Caller.WindowChain babyBearModulus,
      chain.Realizes wrappedData wrappedBefore wrappedCells 4 8 8 12 ∧
      (Cell.register 12).read chain.atFirstFinish = .ok 1 chain.atFirstFinish ∧
      (Cell.register 12).read chain.atSecondFinish = .ok 0 chain.atSecondFinish := by
  obtain ⟨chain, history⟩ := UnifiedReduced.Caller.mixed_window_chain_soundness
    (a := 4) (b := 8) (c := 8) (d := 12)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) wrappedAccepted wrappedInputs
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have firstMatching := UnifiedReduced.Caller.Proofs.matching_at_next_cut (by decide +kernel) (by decide +kernel)
    (lower := 4) (upper := 8) wrappedAccepted.toRequestChecks wrappedInputs.publicProgram
    (by decide) (by decide) (by decide) (by decide) history.firstPrefixMatching history.firstMatching
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair 1 0⟩
  have produced : token ∈ wrappedData.machine.initialMemory ++ (wrappedData.prefixSteps 8).map Prod.snd := by decide +kernel
  have notRead : token ∉ (wrappedData.prefixSteps 8).map Prod.fst := by decide +kernel
  have present : token ∈ chain.firstFinish := by
    rcases List.mem_append.mp (firstMatching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  obtain ⟨cell, _, address, firstRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read history.firstFinishBoundary present
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have finalMatching := UnifiedReduced.Caller.Proofs.matching_at_next_cut (by decide +kernel) (by decide +kernel)
    (lower := 8) (upper := 12) wrappedAccepted.toRequestChecks wrappedInputs.publicProgram
    (by decide) (by decide) (by decide) (by decide) history.secondPrefixMatching history.secondMatching
  have lastRead := UnifiedReduced.Caller.Proofs.preparation_at_boundary (by decide +kernel) (by decide +kernel)
    wrappedAccepted wrappedInputs wrappedPreparation (by decide) (by decide) finalMatching history.secondFinishBoundary
  have bits : token.word.toBitVec = (1 : BitVec 32) := by
    simp only [token, MemoryToken.word, Nat.unpair_pair]
    rfl
  rw [bits] at firstRead
  exact ⟨chain, history, firstRead, lastRead.1⟩

theorem wrapped_profile_excludes_jump (imm : BitVec 21) (rd : BitVec 5) :
    ¬ UnifiedReduced.Caller.WrappedSequentialInstruction (.JAL (imm, .Regidx rd)) := by
  intro supported
  cases supported with
  | sequential supported =>
    cases supported with
    | arithmetic supported => cases supported

theorem wrapped_profile_rejects_misaligned_code :
    ¬ UnifiedReduced.Caller.WrappedSequentialProgram [{ wrappedCompareEntry with pc := 0xfffffffd }] := by
  intro registry
  have alignment := registry.aligned { wrappedCompareEntry with pc := 0xfffffffd } (by simp)
  exact (by decide +kernel : ¬ (0xfffffffd : BitVec 32).toNat % 4 = 0) alignment

theorem wrapped_preparation_wrong_literal_rejected :
    ¬ UnifiedReduced.Caller.ControlPreparation wrappedData wrappedProgram 12 12 (.addi 128) := by
  intro scope
  have instruction := UnifiedReduced.Caller.Proofs.preparation_instruction (by decide +kernel) (by decide +kernel)
    wrappedAccepted wrappedInputs.publicProgram wrappedInputs.ordinaryProgram scope
    (row := wrappedResetRow) (by simp [wrappedData]) (by decide +kernel)
    (entry := wrappedResetEntry) (by simp [wrappedProgram]) (by decide +kernel)
  change SailRV32.instruction.ITYPE (0, .Regidx 0, .Regidx 12, .ADDI) =
    SailRV32.instruction.ITYPE (128, .Regidx 0, .Regidx 12, .ADDI) at instruction
  cases instruction

private def badWrappedData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { wrappedData with machine := { wrappedData.machine with
    rows := [⟨.machine, fun column => if column = 48 then 2 else wrappedResetAssignment column⟩, wrappedCompareRow] } }

theorem wrapped_preparation_fabricated_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted badWrappedData wrappedProgram := by
  intro accepted
  exact (by decide +kernel : ¬
    (badWrappedData.machine.initialMemory ++ badWrappedData.mixedSteps.map Prod.snd).Perm
      (badWrappedData.machine.terminalMemory ++ badWrappedData.mixedSteps.map Prod.fst)) accepted.memory

/-- Unordered native rows still lie in the public clock interval across PC wrap. -/
theorem wrapped_native_clock_interval_derived :
    ∀ row ∈ wrappedData.machine.rows,
      4 ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row + 4 ≤ 12 :=
  Trace.Proofs.state_clock_interval (by decide +kernel) (by decide +kernel)
    wrappedAccepted.constraints wrappedAccepted.states wrappedInputs.publicProgram.initialClock
    wrappedInputs.publicProgram.initialAligned

end Tests.UnifiedComparison
