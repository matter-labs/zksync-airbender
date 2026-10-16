import Tests.TraceExecution
import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Review.Trace.UnifiedReduced.NativeMixedROM

set_option Elab.async false

namespace Tests.UnifiedROMBoot
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

private def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32)
    mem := Tests.TraceExecution.before.mem.insert 0 (0x83 : BitVec 8)
      |>.insert 1 0x20 |>.insert 2 0 |>.insert 3 0 }

private def cells : List Cell := Tests.TraceExecution.cells ++ [.ram 0]
private def physical : List (MemoryToken babyBearModulus) :=
  ROMView.nativeBootImage Tests.TraceExecution.cells ++ [Cell.initialToken (.ram 0) 0x2083]

private def assignment : Nat → ZMod babyBearModulus
  | 4 | 7 | 28 | 44 | 54 | 87 | 129 | 130 | 131 | 132 | 133 => 1
  | 2 | 30 => 4
  | 32 => 8
  | 50 | 90 => 0x2083
  | 86 => 65472
  | 88 => 34
  | _ => 0

private def nativeRow : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment⟩
private def terminal : List (MemoryToken babyBearModulus) :=
  [⟨(Cell.register 0).addressCode, (4, 0), Nat.pair 0 0⟩,
   ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 0x2083 0⟩] ++
  (ROMView.nativeBootImage (p := babyBearModulus) Tests.TraceExecution.cells).drop 2 ++
  [⟨(Cell.ram 0).addressCode, (5, 0), Nat.pair 0 0⟩]

private def trace : UnifiedTrace babyBearModulus where
  rows := [nativeRow]
  rom := UnifiedReduced.Setup.table before
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := ROMView.nativeBootImage cells
  terminalMemory := terminal

private def entry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0x2083, .LOAD (0, .Regidx 0, .Regidx 1, false, 4),
    ⟨.machine, 0, 0, 1, ⟨0, 0⟩, 131072, 0⟩⟩

private theorem bytes : (Cell.ram 0).read before = .ok 0x2083 before := by
  simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]

private theorem zero_registers : ∀ index, (Cell.register index).read before = .ok 0 before := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before = .ok 0 before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
  intro index
  simpa using numeric index.toNat index.isLt

private theorem image : initialImage before cells = some physical := by
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.cons_append, List.nil_append,
    List.mapM_cons, List.mapM_nil, zero_registers, bytes, bind, Option.bind]
  rfl

private theorem profile : InitialProfile before cells := by
  refine ⟨?_, zero_registers, ?_⟩
  · apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · intro address member bound
    have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
    subst address
    change 4194304 ≤ 0 at bound
    omega

private theorem configuration : FlatMemoryConfiguration before := by
  have written : run (SailRV32.Functions.wX_bits (.Regidx 1) 0)
      Tests.TraceExecution.before = .ok ()
        { Tests.TraceExecution.before with regs := Tests.TraceExecution.before.regs.insert .x1 0 } := by
    simp only [SailRV32.Functions.wX_bits, SailRV32.Functions.wX,
      SailRV32.Functions.regval_into_reg, write_callback_pure, freeM_pure_bind]
    exact run_bind_of_ok _ _ _ _ _ (write_register .x1 0 Tests.TraceExecution.before)
  have preserved := configuration_gpr_write Tests.TraceExecution.configuration 1 0 written
  exact configuration_register_frame
    (before := { Tests.TraceExecution.before with
      regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32) })
    (after := before) rfl preserved

private theorem public_inputs : UnifiedReduced.BootInputs trace before cells [entry] := by
  refine ⟨by decide, ?_, profile, ⟨physical, image⟩, rfl, rfl, ⟨[0], ?_⟩, rfl⟩
  · intro cell member
    simp [cells, Tests.TraceExecution.cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, bind, Option.bind, pure]
    with_unfolding_all rfl

private theorem public_word : ROM.words before 0 = 0x2083 := by
  change (match (Cell.ram 0).read before with
    | .ok value _ => value | .error _ _ => 0) = 0x2083
  rw [bytes]

private theorem constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (UnifiedReduced.clockConstraints trace.rom) := by
  apply Verification.holds_append
  · simp [UnifiedReduced.importedConstraints, trace, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, assignment, Lookup.Contains, Table.toRaw, fromElements]
    repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (exact ⟨⟨0, by decide⟩, by with_unfolding_all decide⟩)
      | (refine ⟨⟨1048961, by decide⟩, ?_⟩
         change _ = (#v[0, (Word.ofBitVec (ROM.words before 0)).lo,
           (Word.ofBitVec (ROM.words before 0)).hi, 0, 0, 0, 0, 0, 0, 34] : Vector Nat 10).map
             (fun (n : Nat) => (n : ZMod babyBearModulus))
         rw [public_word]
         with_unfolding_all decide)
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem decoded : UnifiedReduced.Decoded trace [entry] := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change ∃ i : Fin 1, _
  exact ⟨0, by decide⟩

private def mapped := UnifiedReduced.ROMView.row before nativeRow
private def input : Airbender.WordMemory.Input :=
  ⟨false, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x2083, 0⟩, ⟨0, 0⟩,
    .Regidx 0, .Regidx 0, .Regidx 1, 0, Trace.retiredState before 0⟩
private def output : Airbender.WordMemory.Output := ⟨⟨0, 0⟩, ⟨0x2083, 0⟩, ⟨4, 0⟩⟩

private theorem mapped_word : Trace.ROMView.publicWord before (Nat.pair 1 (Nat.pair 0 0)) =
    Word.ofBitVec 0x2083 := by
  have result := Trace.ROMView.public_word_read bytes
  simpa [Cell.addressCode, Word.ofBitVec] using result

theorem memory_transport : UnifiedReduced.MemoryExecution (UnifiedReduced.ROMView.data before trace) before cells :=
  UnifiedReduced.native_rom_memory_execution (by decide) (by decide) accepted public_inputs decoded

theorem sail_rom_load [MemoryPlatform SailRV32.exception] : Airbender.WordMemory.spec input output := by
  apply UnifiedReduced.WordMemory.NativeROM.soundness (by decide) (by decide)
    trace before cells [entry] input output mapped.assignment
  refine ⟨⟨public_inputs, configuration, ?_, by decide⟩,
    ⟨accepted, decoded, by simp [UnifiedReduced.ROMView.data, trace, mapped]⟩, ?_⟩
  · intro address member
    have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
    subst address
    unfold OrdinaryWordAddress
    decide
  · constructor
    · constructor
      all_goals simp [input, output, mapped, UnifiedReduced.ROMView.row, nativeRow, assignment,
        mapped_word, UnifiedReduced.ROMView.readData, Word.ofBitVec, limbBase]
      all_goals decide
    · exact ⟨[], [], before, List.Perm.refl _, by simp, WriteHistory.nil _, rfl⟩
    · refine ⟨entry, by simp, ?_, rfl⟩
      have preserved := UnifiedReduced.ROMView.row_query before nativeRow
      simpa [mapped, UnifiedReduced.decoderQuery, Row.decoderQuery, Row.decoderColumns, Row.columns, CircuitLayout.decoderColumns,
        CircuitLayout.columns, UnifiedReduced.importedConstraintsDecoderColumns,
        UnifiedReduced.importedConstraintsTraceColumns] using preserved.trans (by decide)

private theorem execution_inputs : UnifiedReduced.ExecutionInputs trace before cells [entry] := by
  refine ⟨public_inputs, ?_, ?_, configuration, ?_, ?_, ?_⟩
  · intro index
    have numeric : ∀ n : Nat, n < 32 → Cell.register (BitVec.ofNat 5 n) ∈ cells := by
      intro n bound
      interval_cases n <;> simp [cells, Tests.TraceExecution.cells]
    simpa using numeric index.toNat index.isLt
  · intro actual present
    have same := List.mem_singleton.mp present
    subst actual
    decide
  · intro address member
    have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
    subst address
    unfold OrdinaryWordAddress
    decide
  · rintro ⟨actual, present, imm, rs1, rd, encoding⟩
    have same := List.mem_singleton.mp present
    subst actual
    cases encoding
  · intro actual present imm rs1
    have same := List.mem_singleton.mp present
    subst actual
    simp [entry]

theorem sail_complete_trace [MemoryPlatform SailRV32.exception] :
    Realizes (UnifiedReduced.Step [entry]) trace before cells (Trace.ROMView.token before) :=
  UnifiedReduced.execution_soundness (by decide) (by decide) (by decide) execution_inputs accepted decoded

private def mixedNative : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := trace
  workers :=
    { rows := []
      setup := Delegation.modeledSetup Keccak.Controller.rows
      initial := []
      terminal := [] }
  program := []

private theorem mixedNativeAccepted : UnifiedReduced.Caller.MixedMemoryAccepted mixedNative [entry] := by
  constructor
  · constructor
    · exact accepted.constraints
    · exact accepted.active
    · exact accepted.states
    · intro row member
      have empty : mixedNative.callers = [] := by decide +kernel
      rw [empty] at member
      contradiction
    · intro row member; cases member
    · intro row member; cases member
    · exact List.Perm.refl _
  · intro row member _
    exact decoded row member
  · simpa [mixedNative, UnifiedReduced.Caller.RequestTrace.mixedSteps,
      UnifiedReduced.Caller.machinePorts, UnifiedReduced.Caller.Selected,
      trace, nativeRow, assignment, UnifiedReduced.importedConstraintsDecoderColumns,
      Delegation.MemoryData.steps, Row.reads, Row.writes, Function.comp_def] using accepted.memory

private theorem mixedBoot : UnifiedReduced.Caller.NativeROM.Inputs mixedNative [entry] before cells := by
  constructor
  · refine ⟨public_inputs.distinct, public_inputs.aligned, profile, ⟨physical, image⟩,
      rfl, rfl, ⟨[0], ?_⟩, rfl⟩
    simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, bind, Option.bind, pure]
    with_unfolding_all rfl
  · exact ⟨[], rfl⟩
  · rfl
  · intro row member; cases member

theorem mixed_native_rom_execution :
    UnifiedReduced.Caller.MixedMemoryEffects
      (UnifiedReduced.Caller.NativeROM.view before mixedNative) before cells :=
  UnifiedReduced.Caller.NativeROM.memory_soundness mixedNativeAccepted mixedBoot
    (by intro row member; cases member)

end Tests.UnifiedROMBoot
