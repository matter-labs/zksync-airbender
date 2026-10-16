import Tests.UnifiedDelegationShared

namespace Tests.UnifiedDelegation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private abbrev abiAssignment := BigintFixtures.abiAssignment
private def abiWorker (highControl : Bool) : Delegation.Row babyBearModulus := ⟨.bigint, (abiAssignment highControl)⟩
private def abiBefore (highControl : Bool) : State := wordWriteState
  { Tests.BigintMemory.before with regs := Tests.BigintMemory.before.regs.insert .x12 (if highControl then 65537 else 0) }
  0 (Tests.DelegationCaller.entry .bigint).bits
private def abiData (highControl : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [sharedCaller]
    rom := UnifiedReduced.Setup.table (abiBefore highControl)
    initial := sharedCaller.start
    terminal := sharedCaller.finish
    initialMemory := (Cell.register 0).initialToken 0 :: (abiWorker highControl).memorySteps.map Prod.fst
    terminalMemory := UnifiedReduced.Caller.destinationToken sharedAssignment :: (abiWorker highControl).memorySteps.map Prod.snd }
  workers := {
    setup := Delegation.modeledSetup Keccak.Controller.rows
    rows := [abiWorker highControl]
    initial := (abiWorker highControl).memorySteps.map Prod.fst
    terminal := (abiWorker highControl).memorySteps.map Prod.snd }
  program := [Tests.DelegationCaller.entry .bigint]

private theorem abiCore (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl))
    (Bigint.importedConstraints Bigint.setupTable) := BigintFixtures.abiCore highControl

private theorem abiTimestamps (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl)) Bigint.importedConstraintsTimestampLookups := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, abiAssignment, BigintFixtures.abiAssignment, Tests.BigintMemory.row]
  all_goals decide +kernel

private theorem abiAccepted (highControl : Bool) : UnifiedReduced.Caller.MixedMemoryAccepted (abiData highControl) [] := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (callerCoreFor (abiBefore highControl)) sharedTimestamps
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      decide +kernel
    · exact List.Perm.swap _ _ []
    · intro row member
      have same : row = sharedCaller := List.mem_singleton.mp (List.mem_filter.mp member).1
      subst row
      change ∃ i : Fin 1, UnifiedReduced.decoderQuery sharedAssignment =
        Delegation.Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
      exact ⟨0, by decide +kernel⟩
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (abiCore highControl) (abiTimestamps highControl)
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      change (1 : ZMod babyBearModulus) = 1
      rfl
    · have equal : (abiData highControl).calls = (abiData highControl).fulfillments := by
        cases highControl <;> decide +kernel
      rw [← equal]
      exact List.perm_append_comm
  · intro row member noncaller
    have same : row = sharedCaller := List.mem_singleton.mp member
    subst row
    exact False.elim (noncaller (by
      change sharedCaller ∈ [sharedCaller]
      exact List.mem_singleton_self _))
  · cases highControl <;> decide +kernel

private theorem abiInitialized (highControl : Bool) : initialImage (abiBefore highControl) cells = some (abiData highControl).machine.initialMemory := by
  have x0 : (Cell.register 0).read (abiBefore highControl) = .ok 0 (abiBefore highControl) := by rfl
  have x10 : (Cell.register 10).read (abiBefore highControl) = .ok 4194304 (abiBefore highControl) := by
    apply read_register
    simp [abiBefore, wordWriteState, Tests.BigintMemory.before, Std.ExtDHashMap.get?_insert]
  have x11 : (Cell.register 11).read (abiBefore highControl) = .ok 4194336 (abiBefore highControl) := by
    apply read_register
    simp [abiBefore, wordWriteState, Tests.BigintMemory.before, Std.ExtDHashMap.get?_insert]
  have x12 : (Cell.register 12).read (abiBefore highControl) =
      .ok (if highControl then 65537 else 0) (abiBefore highControl) := by
    apply read_register
    simp [abiBefore, wordWriteState]
  cases highControl <;>
    norm_num [cells, Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells,
    List.range_succ, initialImage, List.mapM_cons, List.mapM_nil, x0, x10, x11, x12]
  all_goals simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get,
    EStateM.pure, abiBefore, wordWriteState, Tests.BigintMemory.before, List.range_succ,
    Std.ExtHashMap.getElem_insert, Cell.initialToken, abiData, abiWorker,
    Delegation.Row.memorySteps, Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, abiAssignment, BigintFixtures.abiAssignment, Tests.BigintMemory.row,
    Word.ofBitVec, limbBase]
  all_goals decide +kernel

private theorem abiInputs (highControl : Bool) : UnifiedReduced.Caller.MixedMemoryInputs (abiData highControl) [] (abiBefore highControl) [0] [] cells := by
  refine ⟨?_, rfl, abiInitialized highControl, Tests.DelegationOperationEffects.sharedInputs.distinct,
    Tests.DelegationOperationEffects.sharedInputs.aligned, rfl, rfl, ?_⟩
  · constructor
    · have bytes : (Cell.ram 0).read (abiBefore highControl) =
          .ok (Tests.DelegationCaller.entry .bigint).bits (abiBefore highControl) := written_word_read _ 0 _
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) (abiBefore highControl) =
          .ok (Tests.DelegationCaller.entry .bigint).instruction (abiBefore highControl) :=
        Tests.DelegationCaller.original_decoder .bigint (abiBefore highControl)
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      exact Trace.Proofs.program_image_run_singleton_of_reads
        Delegation.Caller.decoderFields (abiBefore highControl) (Tests.DelegationCaller.entry .bigint) bytes decoded fields
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · change (4 : Nat) % 4 = 0
      decide +kernel
  · intro row member family
    have same := List.mem_singleton.mp member
    subst row
    cases family

private theorem abiCode (highControl : Bool) :
    UnifiedReduced.Caller.CodeProfile (abiData highControl) [] cells := by
  constructor
  · intro address member
    simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
    rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
    all_goals interval_cases i <;> decide +kernel
  · intro entry present
    cases present
  · intro entry present
    have same := List.mem_singleton.mp present
    subst entry
    change (0 : Nat) < ROM.limit ∧ (0 : Nat) % 4 = 0
    decide +kernel

private theorem abiCurrentFetch (highControl : Bool) : ∃ events finalState,
    events.Perm ((abiData highControl).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (abiBefore highControl) finalState ∧
    UnifiedReduced.Caller.CurrentFetch (abiData highControl) [] (abiBefore highControl) cells events :=
  UnifiedReduced.Caller.current_fetch_soundness (abiAccepted highControl) (abiInputs highControl) (abiCode highControl)

theorem issued_bigint_abi_gap_caller_cycles (highControl : Bool) :
    UnifiedReduced.Caller.CallerCycleEffects (abiData highControl) [] (abiBefore highControl) cells :=
  UnifiedReduced.Caller.caller_cycles_soundness (abiAccepted highControl) (abiInputs highControl) (abiCode highControl)
    (by change (0 : Nat) < 4; decide)

theorem issued_bigint_without_opcode :
    UnifiedReduced.Caller.MixedMemoryAccepted (abiData false) [] ∧
    UnifiedReduced.Caller.MixedMemoryInputs (abiData false) [] (abiBefore false) [0] [] cells ∧
    Delegation.Requests.Live (Delegation.Requests.fulfillment (abiWorker false)) ∧
    (Cell.register 12).read (abiBefore false) = .ok 0 (abiBefore false) ∧
    (∑ i : Fin 7, ((abiAssignment false) Bigint.Variables.operations[i]).val) = 0 := by
  refine ⟨(abiAccepted false), (abiInputs false), ?_, ?_, ?_⟩
  · decide +kernel
  · apply read_register
    simp [abiBefore, wordWriteState]
  · decide +kernel

theorem issued_bigint_without_opcode_execution :
    UnifiedReduced.Caller.MixedMemoryEffects (abiData false) (abiBefore false) cells :=
  UnifiedReduced.Caller.mixed_memory_soundness (abiAccepted false) (abiInputs false)

theorem issued_bigint_without_opcode_current_fetch : ∃ events finalState,
    events.Perm ((abiData false).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (abiBefore false) finalState ∧
    UnifiedReduced.Caller.CurrentFetch (abiData false) [] (abiBefore false) cells events :=
  abiCurrentFetch false

theorem issued_bigint_high_control :
    UnifiedReduced.Caller.MixedMemoryAccepted (abiData true) [] ∧
    UnifiedReduced.Caller.MixedMemoryInputs (abiData true) [] (abiBefore true) [0] [] cells ∧
    Delegation.Requests.Live (Delegation.Requests.fulfillment (abiWorker true)) ∧
    (Cell.register 12).read (abiBefore true) = .ok 65537 (abiBefore true) ∧
    (∑ i : Fin 7, (abiAssignment true Bigint.Variables.operations[i]).val) = 1 := by
  refine ⟨abiAccepted true, abiInputs true, ?_, ?_, ?_⟩
  · decide +kernel
  · apply read_register
    simp [abiBefore, wordWriteState]
  · decide +kernel

theorem issued_bigint_high_control_execution :
    UnifiedReduced.Caller.MixedMemoryEffects (abiData true) (abiBefore true) cells :=
  UnifiedReduced.Caller.mixed_memory_soundness (abiAccepted true) (abiInputs true)

theorem issued_bigint_high_control_current_fetch : ∃ events finalState,
    events.Perm ((abiData true).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (abiBefore true) finalState ∧
    UnifiedReduced.Caller.CurrentFetch (abiData true) [] (abiBefore true) cells events :=
  abiCurrentFetch true


theorem issued_bigint_pointer_abi (highControl : Bool) :
    Bigint.Addresses.PointerABI (Bigint.Addresses.nativeInput (abiAssignment highControl)) := by
  refine UnifiedReduced.Caller.bigint_pointer_soundness (abiAccepted highControl) (abiInputs highControl)
    ?_ (abiWorker highControl) (List.mem_singleton_self _) rfl
  intro address member
  simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
  rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
  all_goals interval_cases i <;> decide +kernel

private def abiNoWorkerBoundaries (highControl : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { abiData highControl with workers := { (abiData highControl).workers with initial := [], terminal := [] } }

theorem unified_projected_worker_boundaries (highControl : Bool) :
    (abiNoWorkerBoundaries highControl).workers.initial = [] ∧
    (abiNoWorkerBoundaries highControl).workers.terminal = [] ∧
    Delegation.MemoryAccepted (abiNoWorkerBoundaries highControl).workerProjection ∧
    Delegation.MemoryInputs (abiNoWorkerBoundaries highControl).workerProjection
      (abiBefore highControl) (Delegation.Caller.workerCells cells) := by
  have old := abiAccepted highControl
  have checks : UnifiedReduced.Caller.RequestChecks (abiNoWorkerBoundaries highControl) :=
    ⟨old.constraints, old.active, old.states, old.decoded, old.workerConstraints, old.workerActive, old.requests⟩
  have accepted : UnifiedReduced.Caller.MixedMemoryAccepted (abiNoWorkerBoundaries highControl) [] :=
    ⟨checks, old.ordinaryDecoded, old.memory⟩
  have inputs := abiInputs highControl
  have publicProgram : UnifiedReduced.Caller.RequestInputs (abiNoWorkerBoundaries highControl)
      (abiBefore highControl) [0] :=
    ⟨inputs.publicProgram.image, inputs.publicProgram.initialClock, inputs.publicProgram.initialAligned⟩
  have requests := UnifiedReduced.Caller.request_soundness (p := babyBearModulus)
    (by norm_num [timestampBase, babyBearModulus]) (by decide +kernel)
    accepted.toRequestChecks publicProgram
  exact ⟨rfl, rfl, UnifiedReduced.Caller.Proofs.worker_projection_accepted accepted requests,
    UnifiedReduced.Caller.Proofs.worker_projection_inputs inputs.initialization inputs.distinct requests⟩

private theorem mixedSequential : UnifiedReduced.Caller.SequentialProgram mixedProgram := by
  intro entry member
  have same : entry = mixedProgram[0] := List.mem_singleton.mp member
  subst entry
  exact .arithmetic (.addi 1 12 12)

private theorem publicCopyRegion :
    UnifiedReduced.Caller.ProgramCallerRegion (mixedData 0) mixedProgram .bigint 4 8 := by
  constructor
  · intro entry member
    have same : entry = mixedProgram[0] := List.mem_singleton.mp member
    subst entry
    decide +kernel
  · intro entry member _
    have same : entry = Tests.DelegationCaller.entry .bigint := List.mem_singleton.mp member
    subst entry
    rfl

theorem program_derived_copy_window :
    UnifiedReduced.Caller.ProgramCallerWindow (mixedData 0) .bigint 4 8 :=
  UnifiedReduced.Caller.program_window_schedule_soundness (by decide +kernel) (by decide +kernel)
    mixedAccepted mixedInputs.publicProgram mixedInputs.ordinaryProgram mixedSequential publicCopyRegion
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem program_derived_copy_count :
    ((mixedData 0).workers.windowRows 4 8).length = 1 ∧
      ∀ worker ∈ (mixedData 0).workers.windowRows 4 8, worker.family = .bigint := by
  have schedule := program_derived_copy_window
  exact ⟨schedule.workerCount.symm.trans (schedule.machineCount.trans (by decide)), schedule.family⟩

private theorem mixedWrapped : UnifiedReduced.Caller.WrappedSequentialProgram mixedProgram := by
  refine ⟨fun entry member => .sequential (mixedSequential entry member), ?_⟩
  intro entry member
  have same : entry = mixedProgram[0] := List.mem_singleton.mp member
  subst entry
  decide +kernel

private theorem wrappedCopyRegion :
    UnifiedReduced.Caller.WrappedProgramCallerRegion (mixedData 0) mixedProgram .bigint 4 8 := by
  constructor
  · intro entry member clock lower upper
    have same : entry = mixedProgram[0] := List.mem_singleton.mp member
    subst entry
    interval_cases clock <;> decide +kernel
  · intro entry member _ _ _ _
    have same : entry = Tests.DelegationCaller.entry .bigint := List.mem_singleton.mp member
    subst entry
    rfl

theorem wrapped_program_derived_copy_window :
    UnifiedReduced.Caller.ProgramCallerWindow (mixedData 0) .bigint 4 8 :=
  UnifiedReduced.Caller.wrapped_program_window_schedule_soundness (by decide +kernel) (by decide +kernel)
    mixedInputs.setup mixedAccepted mixedInputs.publicProgram mixedInputs.ordinaryProgram mixedWrapped wrappedCopyRegion
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem wrapped_public_region_wrong_family_rejected :
    ¬ UnifiedReduced.Caller.WrappedProgramCallerRegion (mixedData 0) mixedProgram .keccak 4 8 := by
  intro region
  have family := region.callers (Tests.DelegationCaller.entry .bigint) (List.mem_singleton_self _)
    4 (by decide) (by decide) (by decide +kernel)
  cases family

theorem wrapped_public_region_including_ordinary_rejected :
    ¬ UnifiedReduced.Caller.WrappedProgramCallerRegion (mixedData 0) mixedProgram .bigint 8 12 := by
  intro region
  exact region.ordinary mixedProgram[0] (List.mem_singleton_self _) 8 (by decide) (by decide) (by decide +kernel)

theorem wrapped_program_region_keeps_bigint_abi_gaps (highControl : Bool) :
    UnifiedReduced.Caller.ProgramCallerWindow (abiData highControl) .bigint 4 8 := by
  have registry : UnifiedReduced.Caller.WrappedSequentialProgram [] := by
    constructor <;> intro entry member <;> cases member
  have region : UnifiedReduced.Caller.WrappedProgramCallerRegion (abiData highControl) [] .bigint 4 8 := by
    constructor
    · intro entry member; cases member
    · intro entry member _ _ _ _
      have same : entry = Tests.DelegationCaller.entry .bigint := List.mem_singleton.mp member
      subst entry
      rfl
  exact UnifiedReduced.Caller.wrapped_program_window_schedule_soundness (by decide +kernel) (by decide +kernel)
    (abiInputs highControl).setup (abiAccepted highControl) (abiInputs highControl).publicProgram
    (abiInputs highControl).ordinaryProgram registry region
    (by decide) (by decide) (by decide) (by decide) (by change 4 ≤ 4; decide) (by change 8 ≤ 8; decide)

theorem public_region_wrong_family_rejected :
    ¬ UnifiedReduced.Caller.ProgramCallerRegion (mixedData 0) mixedProgram .keccak 4 8 := by
  intro region
  have family := region.callers (Tests.DelegationCaller.entry .bigint) (List.mem_singleton_self _)
    (by decide +kernel)
  cases family

theorem program_round_region_wrong_family_rejected :
    ¬ UnifiedReduced.Caller.ProgramRoundRegionInputs (mixedData 0) mixedProgram ⟨0, 4, 8⟩ := by
  intro scope
  have family := scope.code.callers (Tests.DelegationCaller.entry .bigint) (List.mem_singleton_self _)
    (by decide +kernel)
  cases family

theorem public_region_including_ordinary_rejected :
    ¬ UnifiedReduced.Caller.ProgramCallerRegion (mixedData 0) mixedProgram .bigint 8 12 := by
  intro region
  exact region.ordinary mixedProgram[0] (List.mem_singleton_self _) (by decide +kernel)

theorem program_empty_region_after_preparation :
    UnifiedReduced.Caller.ProgramCallerWindow (mixedData 0) .keccak 12 12 := by
  have region : UnifiedReduced.Caller.ProgramCallerRegion (mixedData 0) mixedProgram .keccak 12 12 := by
    constructor
    · intro entry _ range; omega
    · intro entry _ range; omega
  exact UnifiedReduced.Caller.program_window_schedule_soundness (by decide +kernel) (by decide +kernel)
    mixedAccepted mixedInputs.publicProgram mixedInputs.ordinaryProgram mixedSequential region
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem program_region_keeps_bigint_abi_gaps (highControl : Bool) :
    UnifiedReduced.Caller.ProgramCallerWindow (abiData highControl) .bigint 4 8 := by
  have registry : UnifiedReduced.Caller.SequentialProgram [] := by intro entry member; cases member
  have region : UnifiedReduced.Caller.ProgramCallerRegion (abiData highControl) [] .bigint 4 8 := by
    constructor
    · intro entry member; cases member
    · intro entry member _
      have same : entry = Tests.DelegationCaller.entry .bigint := List.mem_singleton.mp member
      subst entry
      rfl
  exact UnifiedReduced.Caller.program_window_schedule_soundness (by decide +kernel) (by decide +kernel)
    (abiAccepted highControl) (abiInputs highControl).publicProgram (abiInputs highControl).ordinaryProgram registry region
    (by decide) (by decide) (by decide) (by decide) (by change 4 ≤ 4; decide) (by change 8 ≤ 8; decide)

private def roundCodeData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { mixedData 0 with program := [Tests.DelegationCaller.entry .blakeRound] }

theorem public_round_csr_requires_a_covering_region :
    UnifiedReduced.Caller.ProgramRoundCallerCoverage roundCodeData [⟨0, 4, 8⟩] ∧
    ¬ UnifiedReduced.Caller.ProgramRoundCallerCoverage roundCodeData [] ∧
    ¬ UnifiedReduced.Caller.ProgramRoundCallerCoverage roundCodeData [⟨0, 8, 8⟩] := by
  refine ⟨?_, ?_, ?_⟩
  · intro entry member _
    have same : entry = Tests.DelegationCaller.entry .blakeRound := List.mem_singleton.mp member
    subst entry
    exact ⟨⟨0, 4, 8⟩, List.mem_singleton_self _, by decide +kernel⟩
  · intro coverage
    obtain ⟨region, member, _⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
      (List.mem_singleton_self _) rfl
    cases member
  · intro coverage
    obtain ⟨region, member, range⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
      (List.mem_singleton_self _) rfl
    have same : region = ⟨0, 8, 8⟩ := List.mem_singleton.mp member
    subst region
    dsimp only at range
    omega

theorem wrapped_public_round_csr_requires_a_covering_occurrence :
    UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage roundCodeData [⟨0, 4, 8⟩] ∧
    ¬ UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage roundCodeData [] ∧
    ¬ UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage roundCodeData [⟨0, 8, 8⟩] := by
  refine ⟨?_, ?_, ?_⟩
  · intro entry member _ clock lower upper _ address
    have same : entry = Tests.DelegationCaller.entry .blakeRound := List.mem_singleton.mp member
    subst entry
    obtain ⟨clockLower, clockUpper⟩ : 4 ≤ clock ∧ clock ≤ 8 := by
      change 4 ≤ clock at lower
      change clock + 4 ≤ 12 at upper
      omega
    interval_cases clock
    all_goals first
      | exact ⟨⟨0, 4, 8⟩, List.mem_singleton_self _, by decide⟩
      | exact absurd address (by decide +kernel)
  · intro coverage
    obtain ⟨region, member, _⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
      (List.mem_singleton_self _) rfl 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    cases member
  · intro coverage
    obtain ⟨region, member, range⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
      (List.mem_singleton_self _) rfl 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    have same : region = ⟨0, 8, 8⟩ := List.mem_singleton.mp member
    subst region
    dsimp only at range
    omega

/-- A public code-policy fixture, without an accepted-trace claim: a round CSR
    address repeats after 2^32 ticks inside the supplied native clock domain. -/
private def repeatedRoundCodeData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { roundCodeData with machine := { roundCodeData.machine with terminal :=
    { roundCodeData.machine.terminal with timestamp := (12, 8192) } } }

theorem wrapped_round_csr_recurrence_requires_both_occurrences :
    UnifiedReduced.Caller.wrappedProgramAddress repeatedRoundCodeData 4 =
      UnifiedReduced.Caller.wrappedProgramAddress repeatedRoundCodeData 4294967300 ∧
    ¬ UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage repeatedRoundCodeData [⟨0, 4, 8⟩] ∧
    ¬ UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage repeatedRoundCodeData [⟨0, 4294967300, 4294967304⟩] := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro coverage
    obtain ⟨region, member, range⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
      (List.mem_singleton_self _) rfl 4294967300
      (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    have same : region = ⟨0, 4, 8⟩ := List.mem_singleton.mp member
    subst region
    dsimp only at range
    omega
  · intro coverage
    obtain ⟨region, member, range⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
      (List.mem_singleton_self _) rfl 4
      (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    have same : region = ⟨0, 4294967300, 4294967304⟩ := List.mem_singleton.mp member
    subst region
    dsimp only at range
    omega

theorem copy_worker_invocation_uniqueness :
    UnifiedReduced.Caller.WorkerInvocationUniqueness (mixedData 0) :=
  UnifiedReduced.Caller.worker_invocation_uniqueness_soundness (by decide +kernel) (by decide +kernel)
    mixedAccepted mixedInputs.publicProgram mixedInputs.initialization mixedInputs.distinct

/-- Clock uniqueness does not impose bigint opcode or high-control validity. -/
theorem invalid_bigint_worker_invocation_uniqueness (highControl : Bool) :
    UnifiedReduced.Caller.WorkerInvocationUniqueness (abiData highControl) :=
  UnifiedReduced.Caller.worker_invocation_uniqueness_soundness (by decide +kernel) (by decide +kernel)
    (abiAccepted highControl) (abiInputs highControl).publicProgram (abiInputs highControl).initialization
    (abiInputs highControl).distinct

theorem copy_all_worker_execution :
    UnifiedReduced.Caller.MixedWorkerExecution (mixedData 0) mixedBefore cells :=
  UnifiedReduced.Caller.all_worker_execution_soundness mixedAccepted mixedInputs

theorem invalid_bigint_all_worker_execution (highControl : Bool) :
    UnifiedReduced.Caller.MixedWorkerExecution (abiData highControl) (abiBefore highControl) cells :=
  UnifiedReduced.Caller.all_worker_execution_soundness (abiAccepted highControl) (abiInputs highControl)

theorem invalid_bigint_native_caller_cycles (highControl : Bool) :
    UnifiedReduced.Caller.CallerCycleEffects (abiData highControl) [] (abiBefore highControl) cells :=
  UnifiedReduced.Caller.native_caller_cycles_soundness (abiAccepted highControl) (abiInputs highControl) (abiCode highControl)

theorem memory_native_caller_cycles (store : Bool) :
    UnifiedReduced.Caller.CallerCycleEffects (memoryData store) [memoryEntry store] (memoryBefore store) cells :=
  UnifiedReduced.Caller.native_caller_cycles_soundness (memoryAccepted store) (memoryInputs store) (memoryCode store)

private def frameSeedEntry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0x07f00693, .ITYPE (127, .Regidx 0, .Regidx 13, .ADDI), ⟨.machine, 0, 0, 13, ⟨127, 0⟩, 1, 0⟩⟩
private def frameLastEntry : UnifiedReduced.ProgramEntry :=
  ⟨8, 0x00168613, .ITYPE (1, .Regidx 13, .Regidx 12, .ADDI), ⟨.machine, 13, 0, 12, ⟨1, 0⟩, 1, 0⟩⟩
private def frameCallerEntry : Delegation.Caller.ProgramEntry :=
  { Tests.DelegationCaller.entry .bigint with pc := 4 }
private def frameProgram : List UnifiedReduced.ProgramEntry := [frameSeedEntry, frameLastEntry]
private def frameBase : State :=
  { Tests.BigintMemory.before with regs := Tests.BigintMemory.before.regs.insert .x13 (0 : BitVec 32) }
private def frameBefore : State :=
  wordWriteState (wordWriteState (wordWriteState frameBase 0 frameSeedEntry.bits) 4 frameCallerEntry.bits) 8 frameLastEntry.bits
private def frameAssignment (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if stage = 1 then
    if column = 0 then 4
    else if column = 2 || column = 30 || column = 46 then 8
    else if column = 32 then 12
    else if column = 34 then 5
    else assignment .bigint column
  else if stage = 0 then
    if column = 2 || column = 30 || column = 40 then 4
    else if column = 32 then 8
    else if column = 7 || column = 44 then 13
    else if column = 8 || column = 50 then 127
    else if column = 4 || column = 11 || column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
    else 0
  else
    if column = 0 then 8
    else if column = 2 || column = 30 then 12
    else if column = 32 then 16
    else if column = 5 then 13
    else if column = 7 || column = 44 then 12
    else if column = 34 then 6
    else if column = 40 then 10
    else if column = 46 then 11
    else if column = 36 then 127
    else if column = 50 then 128
    else if column = 4 || column = 8 || column = 11 || column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
    else 0
private def frameRow (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, frameAssignment stage⟩
private abbrev frameWorkerAssignment := BigintFixtures.frameWorkerAssignment
private def frameWorker : Delegation.Row babyBearModulus := ⟨.bigint, frameWorkerAssignment⟩
private def frameCells : List Cell := .register 13 :: cells
private def frameData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [frameRow 2, frameRow 1, frameRow 0]
    rom := UnifiedReduced.Setup.table frameBefore
    initial := (frameRow 0).start
    terminal := (frameRow 2).finish
    initialMemory := (Cell.register 13).initialToken 0 :: base.machine.initialMemory
    terminalMemory := ⟨(Cell.register 13).addressCode, (12, 0), Nat.pair 127 0⟩ ::
      ⟨(Cell.register 0).addressCode, (13, 0), 0⟩ ::
      (frameWorker.memorySteps.map Prod.snd).map fun token =>
        if token.address = (Cell.register 12).addressCode then ⟨token.address, (14, 0), Nat.pair 128 0⟩ else token }
  workers := { base.workers with rows := [frameWorker] }
  program := [frameCallerEntry]

private theorem frameCore (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (frameAssignment stage)) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table frameBefore)) := by
  fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, frameAssignment, assignment, assignmentWith,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
private theorem frameClocks (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (frameAssignment stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases stage <;> decide +kernel
private theorem frameWorkerCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment frameWorkerAssignment) (Bigint.importedConstraints Bigint.setupTable) :=
  BigintFixtures.frameWorkerCore
private theorem frameWorkerClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment frameWorkerAssignment) Bigint.importedConstraintsTimestampLookups := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, frameWorkerAssignment, BigintFixtures.frameWorkerAssignment, Tests.BigintMemory.row]
  all_goals decide +kernel
private theorem frameAccepted : UnifiedReduced.Caller.MixedMemoryAccepted frameData frameProgram := by
  constructor
  · constructor
    · intro row member
      have rows : row = frameRow 2 ∨ row = frameRow 1 ∨ row = frameRow 0 := by simpa [frameData] using member
      rcases rows with rfl | rfl | rfl
      · exact Verification.holds_append (frameCore 2) (frameClocks 2)
      · exact Verification.holds_append (frameCore 1) (frameClocks 1)
      · exact Verification.holds_append (frameCore 0) (frameClocks 0)
    · intro row member
      have rows : row = frameRow 2 ∨ row = frameRow 1 ∨ row = frameRow 0 := by simpa [frameData] using member
      rcases rows with rfl | rfl | rfl <;> decide +kernel
    · change [(frameRow 0).start, (frameRow 2).finish, (frameRow 1).finish, (frameRow 0).finish].Perm
        [(frameRow 2).finish, (frameRow 2).start, (frameRow 1).start, (frameRow 0).start]
      have first : (frameRow 0).finish = (frameRow 1).start := rfl
      have second : (frameRow 1).finish = (frameRow 2).start := rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro row member
      change row ∈ [frameRow 1] at member
      have same := List.mem_singleton.mp member
      subst row
      exact ⟨(0 : Fin 1), by decide +kernel⟩
    · intro row member
      have same : row = frameWorker := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append frameWorkerCore frameWorkerClocks
    · intro row member
      have same : row = frameWorker := List.mem_singleton.mp member
      subst row
      rfl
    · have equal : frameData.calls = frameData.fulfillments := by decide +kernel
      rw [← equal]
      exact List.perm_append_comm
  · intro row member noncaller
    have rows : row = frameRow 2 ∨ row = frameRow 1 ∨ row = frameRow 0 := by simpa [frameData] using member
    rcases rows with rfl | rfl | rfl
    · exact ⟨(1 : Fin 2), by decide +kernel⟩
    · exact False.elim (noncaller (by change frameRow 1 ∈ [frameRow 1]; exact List.mem_singleton_self _))
    · exact ⟨(0 : Fin 2), by decide +kernel⟩
  · decide +kernel

private theorem frameInitialization : initialImage frameBefore frameCells = some frameData.machine.initialMemory := by
  have x0 : (Cell.register 0).read frameBefore = .ok 0 frameBefore := rfl
  have x10 : (Cell.register 10).read frameBefore = .ok 4194304 frameBefore := by
    apply read_register
    simp [frameBefore, frameBase, wordWriteState, Tests.BigintMemory.before, Std.ExtDHashMap.get?_insert]
  have x11 : (Cell.register 11).read frameBefore = .ok 4194336 frameBefore := by
    apply read_register
    simp [frameBefore, frameBase, wordWriteState, Tests.BigintMemory.before, Std.ExtDHashMap.get?_insert]
  have x12 : (Cell.register 12).read frameBefore = .ok 128 frameBefore := by
    apply read_register
    simp [frameBefore, frameBase, wordWriteState, Tests.BigintMemory.before, Std.ExtDHashMap.get?_insert]
  have x13 : (Cell.register 13).read frameBefore = .ok 0 frameBefore := by
    apply read_register
    simp [frameBefore, frameBase, wordWriteState]
  norm_num [frameCells, cells, Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells,
    List.range_succ, initialImage, List.mapM_cons, List.mapM_nil, x0, x10, x11, x12, x13]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get,
    EStateM.pure, frameBefore, frameBase, wordWriteState, Tests.BigintMemory.before, List.range_succ,
    Std.ExtHashMap.getElem_insert, Cell.initialToken, frameData, base, Tests.DelegationOperationEffects.sharedData,
    frameWorker, Delegation.Row.memorySteps, Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, frameWorkerAssignment, BigintFixtures.frameWorkerAssignment, Tests.BigintMemory.row,
    Word.ofBitVec, limbBase]
  decide +kernel
private theorem frameImage : UnifiedReduced.Mixed.programImage frameBefore [0, 8] = some frameProgram := by
  have first : (Cell.ram 0).read frameBefore = .ok frameSeedEntry.bits frameBefore :=
    written_word_disjoint 8 _ (by decide) (written_word_disjoint 4 _ (by decide) (written_word_read _ 0 _))
  have last : (Cell.ram 8).read frameBefore = .ok frameLastEntry.bits frameBefore := written_word_read _ 8 _
  have df : run (SailRV32.Functions.encdec_backwards frameSeedEntry.bits) frameBefore =
      .ok frameSeedEntry.instruction frameBefore := by with_unfolding_all rfl
  have dl : run (SailRV32.Functions.encdec_backwards frameLastEntry.bits) frameBefore =
      .ok frameLastEntry.instruction frameBefore := by with_unfolding_all rfl
  have mf : UnifiedReduced.Mixed.decoderFields frameSeedEntry.instruction = some frameSeedEntry.data := rfl
  have ml : UnifiedReduced.Mixed.decoderFields frameLastEntry.instruction = some frameLastEntry.data := rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, last, df, dl, mf, ml, bind, Option.bind, pure]
  rfl
private theorem frameInputs : UnifiedReduced.Caller.MixedMemoryInputs frameData frameProgram frameBefore [4] [0, 8] frameCells := by
  refine ⟨?_, frameImage, frameInitialization, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · constructor
    · have bytes : (Cell.ram 4).read frameBefore = .ok frameCallerEntry.bits frameBefore :=
        written_word_disjoint 8 _ (by decide) (written_word_read _ 4 _)
      have decoded : run (SailRV32.Functions.encdec_backwards frameCallerEntry.bits) frameBefore =
          .ok frameCallerEntry.instruction frameBefore := Tests.DelegationCaller.original_decoder .bigint frameBefore
      have fields : Delegation.Caller.decoderFields frameCallerEntry.instruction = some frameCallerEntry.data :=
        Tests.DelegationCaller.metadata .bigint
      exact Trace.Proofs.program_image_run_singleton_of_reads
        Delegation.Caller.decoderFields frameBefore frameCallerEntry bytes decoded fields
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · decide +kernel
  · intro cell member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact Tests.DelegationOperationEffects.sharedInputs.aligned cell member
  · intro worker member family
    have same : worker = frameWorker := List.mem_singleton.mp member
    subst worker
    cases family
private theorem frameRegistry : UnifiedReduced.Caller.WrappedSequentialProgram frameProgram := by
  constructor
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact .sequential (.arithmetic (.addi _ _ _))
    · have same := List.mem_singleton.mp member
      subst entry
      exact .sequential (.arithmetic (.addi _ _ _))
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · have same := List.mem_singleton.mp member
      subst entry
      decide
private theorem frameSeedScope : UnifiedReduced.Caller.ControlPreparation frameData frameProgram 8 13 (.addi 127) := by
  refine ⟨.wrappedSequential (by decide) frameBefore rfl frameRegistry ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro entry member address
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · have same := List.mem_singleton.mp member
    subst entry
    change (8 : BitVec 32) = 0 at address
    contradiction
private theorem frameCallerScope : UnifiedReduced.Caller.CallerFramePreparation frameData frameProgram 12 := by
  refine ⟨frameRegistry, ?_, by decide +kernel, by decide +kernel⟩
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  · have same := List.mem_singleton.mp member
    subst entry
    decide +kernel
private theorem frameLastScope : UnifiedReduced.Caller.RegisterImmediatePreparation frameData frameProgram 16 13 12 1 := by
  refine ⟨frameRegistry, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro entry member address
  rcases List.mem_cons.mp member with rfl | member
  · change (0 : BitVec 32) = 8 at address
    contradiction
  · have same := List.mem_singleton.mp member
    subst entry
    rfl
private theorem framePrior : UnifiedReduced.Caller.PublicRegisterDataflow frameData frameProgram 12 13 127 :=
  .callerFrame (.prepared (.literal frameSeedScope)) frameCallerScope (by decide) (by decide)
private theorem framePreparation : UnifiedReduced.Caller.PublicRegisterDataflow frameData frameProgram 16 12 128 := by
  have step := UnifiedReduced.Caller.PublicRegisterDataflow.addi (cut := 16) framePrior frameLastScope (by decide)
  have value : UnifiedReduced.Caller.registerImmediateValue (127 : BitVec 32) 1 = 128 := by decide +kernel
  exact value ▸ step

theorem caller_gap_preparation : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution frameData frameBefore frameCells 12 13 127 :=
  UnifiedReduced.Caller.Proofs.public_register_dataflow_control_preparation (by decide +kernel) (by decide +kernel)
    (by decide +kernel) frameAccepted frameInputs framePrior (by decide) (by decide)
theorem caller_gap_final_preparation : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution frameData frameBefore frameCells 16 12 128 :=
  UnifiedReduced.Caller.Proofs.public_register_dataflow_control_preparation (by decide +kernel) (by decide +kernel)
    (by decide +kernel) frameAccepted frameInputs framePreparation (by decide) (by decide)

theorem invalid_bigint_caller_gap_refreshes (highControl : Bool) :
    ∀ edge ∈ (abiData highControl).windowSteps 4 8,
      edge.1.address = (Cell.register 11).addressCode → edge.2.value = edge.1.value := by
  apply UnifiedReduced.Caller.Proofs.caller_frame_refreshes (by decide +kernel) (by decide +kernel)
    (abiInputs highControl).setup (abiAccepted highControl) (abiInputs highControl).publicProgram
    (abiInputs highControl).ordinaryProgram (register := 11) (cut := 8)
  · constructor
    · constructor
      · intro _ member
        cases member
      · intro _ member
        cases member
    · intro _ member
      cases member
    · change (8 : Nat) ≤ 8
      decide
    · change (8 : Nat) ≤ 8
      decide
  all_goals decide

theorem caller_gap_protocol_source : UnifiedReduced.Caller.HashControlPreparation frameData frameProgram 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_dataflow_hash_preparation_source frameInputs.initialization
    frameInputs.distinct framePrior frameLastScope (by decide) (by decide +kernel)

theorem caller_gap_protocol_preparation : UnifiedReduced.Caller.PreparedBoundaryExecution frameData frameBefore frameCells 16 12
    (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) frameAccepted frameInputs framePrior frameLastScope
    (by decide) (by decide +kernel) (by decide)

theorem caller_gap_actual_worker_effects :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atGap : State),
      events.Perm ((frameData.prefixSteps 12).map transferEvent) ∧
      SailHistory frameCells events frameBefore atGap ∧
      (Cell.register 13).read atGap = .ok 127 atGap ∧
      (Cell.register 11).read atGap = .ok 4194336 atGap ∧
      (Cell.register 12).read atGap = .ok 0 atGap ∧
      (∃ token ∈ tokens, token.address = (Cell.register 13).addressCode ∧
        (timeOfPair token.time).value = 6 ∧ token.word = Word.ofBitVec 127) ∧
      ∃ token ∈ tokens, token.address = (Cell.register 11).addressCode ∧
        (timeOfPair token.time).value = 11 ∧ token.word = Word.ofBitVec 4194336 := by
  obtain ⟨tokens, _, events, _, atGap, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 12) (upper := 12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) frameAccepted frameInputs
      (by decide) (by decide) (by decide) (by decide)).execution
  let tracked : MemoryToken babyBearModulus := ⟨(Cell.register 13).addressCode, (6, 0), Nat.pair 127 0⟩
  let pointer : MemoryToken babyBearModulus := ⟨(Cell.register 11).addressCode, (11, 0), Nat.pair 32 64⟩
  let control : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (11, 0), 0⟩
  have actual (token : MemoryToken babyBearModulus)
      (produced : token ∈ frameData.machine.initialMemory ++ (frameData.prefixSteps 12).map Prod.snd)
      (notRead : token ∉ (frameData.prefixSteps 12).map Prod.fst) : token ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  have trackedPresent : tracked ∈ tokens := actual tracked (by decide +kernel) (by decide +kernel)
  have pointerPresent : pointer ∈ tokens := actual pointer (by decide +kernel) (by decide +kernel)
  have controlPresent : control ∈ tokens := actual control (by decide +kernel) (by decide +kernel)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary trackedPresent
  have same : cell = Cell.register 13 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, pointerRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary pointerPresent
  have same : cell = Cell.register 11 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, controlRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary controlPresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  have trackedWord : tracked.word = Word.ofBitVec 127 := by decide +kernel
  have pointerWord : pointer.word = Word.ofBitVec 4194336 := by decide +kernel
  have controlWord : control.word = Word.ofBitVec 0 := by decide +kernel
  rw [trackedWord, Word.ofBitVec_roundtrip] at read
  rw [pointerWord, Word.ofBitVec_roundtrip] at pointerRead
  rw [controlWord, Word.ofBitVec_roundtrip] at controlRead
  exact ⟨tokens, events, atGap, permutation, history, read, pointerRead, controlRead,
    ⟨tracked, trackedPresent, rfl, by decide, trackedWord⟩,
    pointer, pointerPresent, rfl, by decide, pointerWord⟩

theorem caller_gap_changes_control :
    ∃ edge ∈ frameData.windowSteps 8 12, edge.1.address = (Cell.register 12).addressCode ∧
      edge.1.word = Word.ofBitVec 128 ∧ edge.2.word = Word.ofBitVec 0 := by
  exact ⟨(frameWorker.memorySteps[18]), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def frameForgedAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 34 then 11 else frameAssignment 2 column
private def frameForgedData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { frameData with machine := { frameData.machine with rows := [⟨.machine, frameForgedAssignment⟩, frameRow 1, frameRow 0] } }
theorem caller_gap_fabricated_source_rejected : ¬ UnifiedReduced.Caller.MixedMemoryAccepted frameForgedData frameProgram := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 13).addressCode, (11, 0), Nat.pair 127 0⟩
  have member : token ∈ frameForgedData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ frameForgedData.machine.initialMemory ++ frameForgedData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))
theorem caller_gap_fabricated_source_native : FlatOperation.ConstraintsHoldFlat
    (Verification.environment frameForgedAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table frameBefore) ++ UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  · simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat, Verification.environment,
      Expression.eval, frameForgedAssignment, frameAssignment, Lookup.Contains, Table.toRaw, fromElements]
    repeat' apply And.intro
    all_goals solve
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
      | (refine ⟨(0 : Fin 2097537), ?_⟩
         change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
           (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals decide +kernel

theorem ordinary_preparation_is_not_caller_gap : ¬ UnifiedReduced.Caller.CallerFramePreparation frameData frameProgram 8 := by
  intro scope
  exact scope.ordinary frameSeedEntry (by simp [frameProgram]) rfl

theorem caller_gap_incomplete_reference_rejected :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs frameData frameProgram ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction

private theorem returnScope {data : UnifiedReduced.Caller.RequestTrace babyBearModulus}
    (families : ∀ entry ∈ data.program, entry.data.family = .bigint)
    (first : (timeOfPair data.machine.initial.timestamp).value = 4)
    (last : (timeOfPair data.machine.terminal.timestamp).value = 8) :
    UnifiedReduced.Caller.CallerControlPreparation data [] .bigint 8 := by
  constructor
  · constructor
    · intro _ member
      cases member
    · intro _ member
      cases member
  · constructor
    · intro _ member
      cases member
    · intro entry member _ _ _ _
      exact families entry member
  · omega
  · omega
private theorem copyReturnScope : UnifiedReduced.Caller.CallerControlPreparation callerOnlyData [] .bigint 8 := by
  apply returnScope
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    rfl
  all_goals rfl
private theorem abiReturnScope (highControl : Bool) :
    UnifiedReduced.Caller.CallerControlPreparation (abiData highControl) [] .bigint 8 := by
  apply returnScope
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    rfl
  all_goals rfl

theorem bigint_return_copy_boundary : UnifiedReduced.Caller.BigintControlBoundaryExecution callerOnlyData mixedBefore cells 8 :=
  UnifiedReduced.Caller.bigint_control_boundary_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) callerOnlyAccepted callerOnlyInputs copyReturnScope (by decide)
theorem bigint_return_invalid_controls (highControl : Bool) :
    UnifiedReduced.Caller.BigintControlBoundaryExecution (abiData highControl) (abiBefore highControl) cells 8 :=
  UnifiedReduced.Caller.bigint_control_boundary_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (abiAccepted highControl) (abiInputs highControl) (abiReturnScope highControl) (by decide)

private abbrev returnCarryAssignment := BigintFixtures.returnCarryAssignment
private def returnCarryWorker : Delegation.Row babyBearModulus := ⟨.bigint, returnCarryAssignment⟩
private def returnCarryBase : State :=
  { Tests.BigintMemory.before with
    regs := Tests.BigintMemory.before.regs.insert .x12 (192 : BitVec 32)
    mem := (List.range 32).foldl (fun memory i => memory.insert (4194336 + i) (255 : BitVec 8)) Tests.BigintMemory.before.mem }
private def returnCarryBefore : State := wordWriteState returnCarryBase 0 (Tests.DelegationCaller.entry .bigint).bits
private def returnCarryData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [sharedCaller]
    rom := UnifiedReduced.Setup.table returnCarryBefore
    initial := sharedCaller.start
    terminal := sharedCaller.finish
    initialMemory := (Cell.register 0).initialToken 0 :: returnCarryWorker.memorySteps.map Prod.fst
    terminalMemory := UnifiedReduced.Caller.destinationToken sharedAssignment :: returnCarryWorker.memorySteps.map Prod.snd }
  workers := { base.workers with rows := [returnCarryWorker], initial := [], terminal := [] }
  program := [Tests.DelegationCaller.entry .bigint]
private theorem returnCarryCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment returnCarryAssignment) (Bigint.importedConstraints Bigint.setupTable) :=
  BigintFixtures.returnCarryCore
private theorem returnCarryClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment returnCarryAssignment) Bigint.importedConstraintsTimestampLookups := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, returnCarryAssignment, BigintFixtures.returnCarryAssignment, Tests.BigintMemory.row]
  all_goals decide +kernel
private theorem returnCarryAccepted : UnifiedReduced.Caller.MixedMemoryAccepted returnCarryData [] := by
  constructor
  · constructor
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (callerCoreFor returnCarryBefore) sharedTimestamps
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      rfl
    · exact List.Perm.swap _ _ []
    · intro row member
      change row ∈ [sharedCaller] at member
      have same := List.mem_singleton.mp member
      subst row
      exact ⟨(0 : Fin 1), by decide +kernel⟩
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append returnCarryCore returnCarryClocks
    · intro row member
      have same := List.mem_singleton.mp member
      subst row
      rfl
    · have equal : returnCarryData.calls = returnCarryData.fulfillments := by decide +kernel
      rw [← equal]
      exact List.perm_append_comm
  · intro row member ordinary
    have same := List.mem_singleton.mp member
    subst row
    exact False.elim (ordinary (by change sharedCaller ∈ [sharedCaller]; exact List.mem_singleton_self _))
  · decide +kernel
private theorem returnCarryInitialization : initialImage returnCarryBefore cells = some returnCarryData.machine.initialMemory := by
  have x0 : (Cell.register 0).read returnCarryBefore = .ok 0 returnCarryBefore := rfl
  have x10 : (Cell.register 10).read returnCarryBefore = .ok 4194304 returnCarryBefore := by
    apply read_register
    simp [returnCarryBefore, returnCarryBase, wordWriteState, Tests.BigintMemory.before, Std.ExtDHashMap.get?_insert]
  have x11 : (Cell.register 11).read returnCarryBefore = .ok 4194336 returnCarryBefore := by
    apply read_register
    simp [returnCarryBefore, returnCarryBase, wordWriteState, Tests.BigintMemory.before, Std.ExtDHashMap.get?_insert]
  have x12 : (Cell.register 12).read returnCarryBefore = .ok 192 returnCarryBefore := by
    apply read_register
    simp [returnCarryBefore, returnCarryBase, wordWriteState]
  norm_num [cells, Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells,
    List.range_succ, initialImage, List.mapM_cons, List.mapM_nil, x0, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get,
    EStateM.pure, returnCarryBefore, returnCarryBase, wordWriteState, Tests.BigintMemory.before, List.range_succ,
    Std.ExtHashMap.getElem_insert, Cell.initialToken, returnCarryData, returnCarryWorker,
    Delegation.Row.memorySteps, Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, returnCarryAssignment, BigintFixtures.returnCarryAssignment, Tests.BigintMemory.row,
    Word.ofBitVec, limbBase]
  decide +kernel
private theorem returnCarryInputs : UnifiedReduced.Caller.MixedMemoryInputs returnCarryData [] returnCarryBefore [0] [] cells := by
  refine ⟨?_, rfl, returnCarryInitialization, callerOnlyInputs.distinct, callerOnlyInputs.aligned, rfl, rfl, ?_⟩
  · constructor
    · have bytes : (Cell.ram 0).read returnCarryBefore = .ok (Tests.DelegationCaller.entry .bigint).bits returnCarryBefore := written_word_read _ 0 _
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) returnCarryBefore =
          .ok (Tests.DelegationCaller.entry .bigint).instruction returnCarryBefore :=
        Tests.DelegationCaller.original_decoder .bigint returnCarryBefore
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      exact Trace.Proofs.program_image_run_singleton_of_reads
        Delegation.Caller.decoderFields returnCarryBefore (Tests.DelegationCaller.entry .bigint) bytes decoded fields
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · decide +kernel
  · intro row member family
    have same := List.mem_singleton.mp member
    subst row
    cases family
private theorem returnCarryScope : UnifiedReduced.Caller.CallerControlPreparation returnCarryData [] .bigint 8 := by
  apply returnScope
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    rfl
  all_goals rfl

theorem bigint_return_carry_boundary : UnifiedReduced.Caller.BigintControlBoundaryExecution returnCarryData returnCarryBefore cells 8 :=
  UnifiedReduced.Caller.bigint_control_boundary_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) returnCarryAccepted returnCarryInputs returnCarryScope (by decide)

theorem bigint_return_wrong_family_rejected : ¬ UnifiedReduced.Caller.CallerControlPreparation callerOnlyData [] .keccak 8 := by
  intro scope
  have family := scope.region.callers (Tests.DelegationCaller.entry .bigint) (by simp [callerOnlyData]) 4 (by decide) (by decide) rfl
  contradiction

theorem bigint_return_past_terminal_rejected : ¬ UnifiedReduced.Caller.CallerControlPreparation callerOnlyData [] .bigint 12 := by
  intro scope
  have terminal := scope.beforeTerminal
  change 12 ≤ 8 at terminal
  omega

theorem bigint_return_ordinary_code_rejected : ¬ UnifiedReduced.Caller.CallerControlPreparation frameData frameProgram .bigint 8 := by
  intro scope
  exact scope.region.ordinary frameSeedEntry (by simp [frameProgram]) 4 (by decide) (by decide) rfl

theorem bigint_return_two_rejected : ¬ FlatOperation.ConstraintsHoldFlat
    (Verification.environment (fun column => if column = 57 then 2 else returnCarryAssignment column))
    (Bigint.importedConstraints Bigint.setupTable) := by
  intro accepted
  have bound := (Bigint.Proofs.returned_control_bounds (by decide : 65536 ≤ babyBearModulus) accepted).1
  have impossible : ¬ ((2 : ZMod babyBearModulus) = 0 ∨ (2 : ZMod babyBearModulus) = 1) := by decide +kernel
  change (2 : ZMod babyBearModulus) = 0 ∨ (2 : ZMod babyBearModulus) = 1 at bound
  exact impossible bound

theorem bigint_return_carry_actual :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (after : State),
      events.Perm ((returnCarryData.prefixSteps 8).map transferEvent) ∧
      SailHistory cells events returnCarryBefore after ∧
      (Cell.register 12).read returnCarryBefore = .ok 192 returnCarryBefore ∧
      (Cell.register 12).read after = .ok 1 after ∧
      (Cell.ram 4194336).read after = .ok 0xffffffff after ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 7 ∧ token.word = Word.ofBitVec 1 := by
  obtain ⟨tokens, events, after, _, permutation, history, matching, boundary, _, _, _⟩ := bigint_return_carry_boundary
  let control := returnCarryWorker.writeToken Bigint.importedConstraintsMemoryPorts[18]
  let source := returnCarryWorker.writeToken Bigint.importedConstraintsMemoryPorts[10]
  have actual (token : MemoryToken babyBearModulus)
      (produced : token ∈ returnCarryData.machine.initialMemory ++ (returnCarryData.prefixSteps 8).map Prod.snd)
      (notRead : token ∉ (returnCarryData.prefixSteps 8).map Prod.fst) : token ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  have present : control ∈ tokens := actual control (by decide +kernel) (by decide +kernel)
  have sourcePresent : source ∈ tokens := actual source (by decide +kernel) (by decide +kernel)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary present
  have equal : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, sourceRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary sourcePresent
  have equal : cell = Cell.ram 4194336 := Trace.Proofs.cell_address_injective code
  subst cell
  have controlWord : control.word = Word.ofBitVec 1 := by decide +kernel
  have sourceWord : source.word = Word.ofBitVec 0xffffffff := by decide +kernel
  rw [controlWord, Word.ofBitVec_roundtrip] at read
  rw [sourceWord, Word.ofBitVec_roundtrip] at sourceRead
  have initial : (Cell.register 12).read returnCarryBefore = .ok 192 returnCarryBefore := by
    apply read_register
    simp [returnCarryBefore, returnCarryBase, wordWriteState]
  exact ⟨tokens, events, after, permutation, history, initial, read, sourceRead,
    control, present, rfl, by decide, controlWord⟩

theorem bigint_return_invalid_actual (highControl : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (after : State),
      events.Perm (((abiData highControl).prefixSteps 8).map transferEvent) ∧
      SailHistory cells events (abiBefore highControl) after ∧
      (Cell.register 12).read (abiBefore highControl) = .ok (if highControl then 65537 else 0) (abiBefore highControl) ∧
      (Cell.register 12).read after = .ok 0 after ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 7 ∧ token.word = Word.ofBitVec 0 := by
  obtain ⟨tokens, events, after, _, permutation, history, matching, boundary, _, _, _⟩ := bigint_return_invalid_controls highControl
  let control := (abiWorker highControl).writeToken Bigint.importedConstraintsMemoryPorts[18]
  have produced : control ∈ (abiData highControl).machine.initialMemory ++ ((abiData highControl).prefixSteps 8).map Prod.snd := by
    cases highControl <;> decide +kernel
  have notRead : control ∉ ((abiData highControl).prefixSteps 8).map Prod.fst := by cases highControl <;> decide +kernel
  have present : control ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary present
  have equal : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  have word : control.word = Word.ofBitVec 0 := by cases highControl <;> decide +kernel
  rw [word, Word.ofBitVec_roundtrip] at read
  have initial : (Cell.register 12).read (abiBefore highControl) =
      .ok (if highControl then 65537 else 0) (abiBefore highControl) := by
    apply read_register
    simp [abiBefore, wordWriteState]
  exact ⟨tokens, events, after, permutation, history, initial, read, control, present, rfl,
    by cases highControl <;> decide, word⟩

/-- COPY return zero, carry return one, and both admitted invalid controls. -/
private def normalizeSeed (kind : Fin 4) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  if kind = 0 then callerOnlyData else if kind = 1 then returnCarryData else abiData (kind = 3)
private def normalizeSeedBefore (kind : Fin 4) : State :=
  if kind = 0 then mixedBefore else if kind = 1 then returnCarryBefore else abiBefore (kind = 3)
private theorem normalizeSeedAccepted (kind : Fin 4) : UnifiedReduced.Caller.MixedMemoryAccepted (normalizeSeed kind) [] := by
  fin_cases kind
  · exact callerOnlyAccepted
  · exact returnCarryAccepted
  · exact abiAccepted false
  · exact abiAccepted true
private theorem normalizeSeedInputs (kind : Fin 4) :
    UnifiedReduced.Caller.MixedMemoryInputs (normalizeSeed kind) [] (normalizeSeedBefore kind) [0] [] cells := by
  fin_cases kind
  · exact callerOnlyInputs
  · exact returnCarryInputs
  · exact abiInputs false
  · exact abiInputs true
private def normalizeEntry : UnifiedReduced.ProgramEntry :=
  ⟨4, 0x00166613, .ITYPE (1, .Regidx 12, .Regidx 12, .ORI), ⟨.machine, 12, 0, 12, ⟨1, 0⟩, 65536, 53⟩⟩
private def normalizeLast : UnifiedReduced.ProgramEntry :=
  ⟨8, 0x07f60613, .ITYPE (127, .Regidx 12, .Regidx 12, .ADDI), ⟨.machine, 12, 0, 12, ⟨127, 0⟩, 1, 0⟩⟩
private def normalizeProgram := [normalizeEntry, normalizeLast]
private def normalizeBefore (kind : Fin 4) : State :=
  wordWriteState (wordWriteState (normalizeSeedBefore kind) 4 normalizeEntry.bits) 8 normalizeLast.bits
private def normalizeAssignment (one : Bool) (stage : Fin 2) (column : Nat) : ZMod babyBearModulus :=
  if stage = 0 then
    if column = 0 then 4
    else if column = 2 || column = 30 || column = 46 then 8
    else if column = 32 || column = 5 || column = 7 || column = 44 then 12
    else if column = 34 then 7
    else if column = 40 then 6
    else if column = 36 || column = 48 || column = 74 || column = 93 then if one then 1 else 0
    else if column = 10 || column = 92 || column = 101 || column = 110 || column = 119 then 53
    else if column = 88 then 3
    else if column = 4 || column = 8 || column = 27 || column = 50 || column = 58 || column = 94 || column = 95 ||
        column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
    else 0
  else
    if column = 0 then 8
    else if column = 2 || column = 30 || column = 5 || column = 7 || column = 44 || column = 46 then 12
    else if column = 32 then 16
    else if column = 34 then 10
    else if column = 40 then 9
    else if column = 8 then 127
    else if column = 50 then 128
    else if column = 4 || column = 11 || column = 36 || column = 48 ||
        column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
    else 0
private def normalizeRow (kind : Fin 4) (stage : Fin 2) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, normalizeAssignment (kind = 1) stage⟩
private def normalizeData (kind : Fin 4) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [normalizeRow kind 1, normalizeRow kind 0, sharedCaller]
    rom := UnifiedReduced.Setup.table (normalizeBefore kind)
    initial := sharedCaller.start
    terminal := (normalizeRow kind 1).finish
    initialMemory := (normalizeSeed kind).machine.initialMemory
    terminalMemory := (normalizeSeed kind).machine.terminalMemory.map fun token =>
      if token.address = (Cell.register 0).addressCode then ⟨token.address, (13, 0), 0⟩
      else if token.address = (Cell.register 12).addressCode then ⟨token.address, (14, 0), Nat.pair 128 0⟩
      else token }
  workers := (normalizeSeed kind).workers
  program := [Tests.DelegationCaller.entry .bigint]
private theorem normalizeCore (state : State) (one : Bool) (stage : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (normalizeAssignment one stage)) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table state)) := by
  cases one <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, normalizeAssignment, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change _ = (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
    | (refine ⟨(1 : Fin 2097537), ?_⟩
       change _ = (UnifiedReduced.Setup.fixedRow (1 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
    | (refine ⟨(65793 : Fin 2097537), ?_⟩
       change _ = (UnifiedReduced.Setup.fixedRow (65793 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
    | (refine ⟨(65794 : Fin 2097537), ?_⟩
       change _ = (UnifiedReduced.Setup.fixedRow (65794 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
    | (refine ⟨(66050 : Fin 2097537), ?_⟩
       change _ = (UnifiedReduced.Setup.fixedRow (66050 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
private theorem normalizeClocks (one : Bool) (stage : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (normalizeAssignment one stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases one <;> fin_cases stage <;> decide +kernel
private theorem normalizeAccepted (kind : Fin 4) : UnifiedReduced.Caller.MixedMemoryAccepted (normalizeData kind) normalizeProgram := by
  constructor
  · constructor
    · intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact Verification.holds_append (normalizeCore _ (decide (kind = 1)) 1) (normalizeClocks (decide (kind = 1)) 1)
      · rcases List.mem_cons.mp member with rfl | member
        · exact Verification.holds_append (normalizeCore _ (decide (kind = 1)) 0) (normalizeClocks (decide (kind = 1)) 0)
        · have same := List.mem_singleton.mp member
          subst row
          exact Verification.holds_append (callerCoreFor _) sharedTimestamps
    · intro row member
      rcases List.mem_cons.mp member with rfl | member
      · fin_cases kind <;> decide +kernel
      · rcases List.mem_cons.mp member with rfl | member
        · fin_cases kind <;> decide +kernel
        · have same := List.mem_singleton.mp member
          subst row
          rfl
    · change [sharedCaller.start, (normalizeRow kind 1).finish, (normalizeRow kind 0).finish, sharedCaller.finish].Perm
        [(normalizeRow kind 1).finish, (normalizeRow kind 1).start, (normalizeRow kind 0).start, sharedCaller.start]
      have first : sharedCaller.finish = (normalizeRow kind 0).start := rfl
      have second : (normalizeRow kind 0).finish = (normalizeRow kind 1).start := rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro row member
      have same : row = sharedCaller := by fin_cases kind <;> exact List.mem_singleton.mp member
      subst row
      change ∃ i : Fin 1, UnifiedReduced.decoderQuery sharedAssignment =
        Delegation.Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
      exact ⟨0, by decide +kernel⟩
    · exact (normalizeSeedAccepted kind).workerConstraints
    · exact (normalizeSeedAccepted kind).workerActive
    · have equal : (normalizeData kind).calls = (normalizeData kind).fulfillments := by fin_cases kind <;> decide +kernel
      rw [← equal]
      exact List.perm_append_comm
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨(1 : Fin 2), by fin_cases kind <;> decide +kernel⟩
    · rcases List.mem_cons.mp member with rfl | member
      · exact ⟨(0 : Fin 2), by fin_cases kind <;> decide +kernel⟩
      · have same := List.mem_singleton.mp member
        subst row
        exact False.elim (noncaller (by fin_cases kind <;> exact List.mem_singleton_self _))
  · fin_cases kind <;> decide +kernel
private theorem normalizeInitialization (kind : Fin 4) :
    initialImage (normalizeBefore kind) cells = some (normalizeData kind).machine.initialMemory := by
  have frame (state : State) (address : Nat) (bits : BitVec 32) (bound : address + 4 ≤ 12)
      {tokens : List (MemoryToken babyBearModulus)} (initialized : initialImage state cells = some tokens) :
      initialImage (wordWriteState state address bits) cells = some tokens := by
    apply Trace.Proofs.image_frame initialized
    intro cell member value read
    cases cell with
    | register index => exact rX_register_frame (by dsimp only [wordWriteState]) index read
    | ram location =>
      have lower : 12 ≤ location.toNat := by
        simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
        rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
        all_goals interval_cases i <;> decide
      exact written_word_disjoint address bits (Or.inr (by omega)) read
  exact frame _ 8 _ (by decide) (frame _ 4 _ (by decide) (normalizeSeedInputs kind).initialization)
private theorem normalizeInputs (kind : Fin 4) :
    UnifiedReduced.Caller.MixedMemoryInputs (normalizeData kind) normalizeProgram (normalizeBefore kind) [0] [4, 8] cells := by
  refine ⟨?_, ?_, normalizeInitialization kind, (normalizeSeedInputs kind).distinct,
    (normalizeSeedInputs kind).aligned, rfl, ?_, ?_⟩
  · constructor
    · have seedRead : (Cell.ram 0).read (normalizeSeedBefore kind) =
          .ok (Tests.DelegationCaller.entry .bigint).bits (normalizeSeedBefore kind) := by
        fin_cases kind
        · exact written_word_disjoint 4 _ (by decide) (written_word_read _ 0 _)
        all_goals exact written_word_read _ 0 _
      have bytes : (Cell.ram 0).read (normalizeBefore kind) =
          .ok (Tests.DelegationCaller.entry .bigint).bits (normalizeBefore kind) :=
        written_word_disjoint 8 _ (by decide) (written_word_disjoint 4 _ (by decide) seedRead)
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) (normalizeBefore kind) =
          .ok (Tests.DelegationCaller.entry .bigint).instruction (normalizeBefore kind) :=
        Tests.DelegationCaller.original_decoder .bigint (normalizeBefore kind)
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      exact Trace.Proofs.program_image_run_singleton_of_reads
        Delegation.Caller.decoderFields (normalizeBefore kind) (Tests.DelegationCaller.entry .bigint) bytes decoded fields
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · change 4 % 4 = 0
      decide
  · have first : (Cell.ram 4).read (normalizeBefore kind) = .ok normalizeEntry.bits (normalizeBefore kind) :=
      written_word_disjoint 8 _ (by decide) (written_word_read _ 4 _)
    have last : (Cell.ram 8).read (normalizeBefore kind) = .ok normalizeLast.bits (normalizeBefore kind) := written_word_read _ 8 _
    have df : run (SailRV32.Functions.encdec_backwards normalizeEntry.bits) (normalizeBefore kind) =
        .ok normalizeEntry.instruction (normalizeBefore kind) := by with_unfolding_all rfl
    have dl : run (SailRV32.Functions.encdec_backwards normalizeLast.bits) (normalizeBefore kind) =
        .ok normalizeLast.instruction (normalizeBefore kind) := by with_unfolding_all rfl
    have mf : UnifiedReduced.Mixed.decoderFields normalizeEntry.instruction = some normalizeEntry.data := rfl
    have ml : UnifiedReduced.Mixed.decoderFields normalizeLast.instruction = some normalizeLast.data := rfl
    simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, first, last, df, dl, mf, ml, bind, Option.bind, pure]
    rfl
  · fin_cases kind <;> rfl
  · intro row member family
    fin_cases kind
    all_goals have same := List.mem_singleton.mp member
    all_goals subst row
    all_goals cases family
private theorem normalizeRegistry : UnifiedReduced.Caller.WrappedSequentialProgram normalizeProgram := by
  constructor
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact .sequential (.ori _ _ _)
    · have same := List.mem_singleton.mp member
      subst entry
      exact .sequential (.arithmetic (.addi _ _ _))
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · have same := List.mem_singleton.mp member
      subst entry
      decide
private theorem normalizeScope (kind : Fin 4) :
    UnifiedReduced.Caller.BigintReturnPreparation (normalizeData kind) normalizeProgram 12 12 := by
  constructor
  · refine ⟨normalizeRegistry, ?_, by change 4 + 4 ≤ 8; decide, by change 8 ≤ 16; decide⟩
    constructor
    · intro entry member clock lower upper address
      rcases List.mem_cons.mp member with rfl | member
      · interval_cases clock
        all_goals exact absurd address (by fin_cases kind <;> decide +kernel)
      · have same := List.mem_singleton.mp member
        subst entry
        interval_cases clock
        all_goals exact absurd address (by fin_cases kind <;> decide +kernel)
    · intro entry member _ _ _ _
      have same := List.mem_singleton.mp member
      subst entry
      rfl
  · fin_cases kind <;> rfl
  · intro entry member address
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · have same := List.mem_singleton.mp member
      subst entry
      have impossible : normalizeLast.pc ≠ UnifiedReduced.Caller.wrappedProgramAddress (normalizeData kind) 8 := by
        fin_cases kind <;> decide +kernel
      exact False.elim (impossible address)
  · fin_cases kind <;> decide +kernel
  · fin_cases kind <;> decide +kernel
private theorem normalizeLastScope (kind : Fin 4) :
    UnifiedReduced.Caller.RegisterImmediatePreparation (normalizeData kind) normalizeProgram 16 12 12 127 := by
  refine ⟨normalizeRegistry, ?_, ?_, by change 4 + 4 ≤ 16; decide, by change 16 ≤ 16; decide⟩
  · intro entry member address
    rcases List.mem_cons.mp member with rfl | member
    · have impossible : normalizeEntry.pc ≠ UnifiedReduced.Caller.wrappedProgramAddress (normalizeData kind) 12 := by
        fin_cases kind <;> decide +kernel
      exact False.elim (impossible address)
    · have same := List.mem_singleton.mp member
      subst entry
      rfl
  · fin_cases kind <;> decide +kernel
private theorem normalizeFlow (kind : Fin 4) :
    UnifiedReduced.Caller.PublicRegisterDataflow (normalizeData kind) normalizeProgram 16 12 128 := by
  have result := UnifiedReduced.Caller.PublicRegisterDataflow.addi (.bigintReturn (normalizeScope kind))
    (normalizeLastScope kind) (by decide)
  exact result

theorem bigint_return_normalized_boundary (kind : Fin 4) :
    UnifiedReduced.Caller.RegisterDataflowBoundaryExecution (normalizeData kind) (normalizeBefore kind) cells 12 12 1 :=
  UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (normalizeAccepted kind) (normalizeInputs kind) (.bigintReturn (normalizeScope kind)) (by decide) (by decide)
theorem bigint_return_normalized_control (kind : Fin 4) :
    UnifiedReduced.Caller.RegisterDataflowBoundaryExecution (normalizeData kind) (normalizeBefore kind) cells 16 12 128 :=
  UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (normalizeAccepted kind) (normalizeInputs kind) (normalizeFlow kind) (by decide) (by decide)

theorem bigint_return_normalized_protocol_source (kind : Fin 4) :
    UnifiedReduced.Caller.HashControlPreparation (normalizeData kind) normalizeProgram 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_dataflow_hash_preparation_source (normalizeInputs kind).initialization
    (normalizeInputs kind).distinct (.bigintReturn (normalizeScope kind)) (normalizeLastScope kind) (by decide) (by decide +kernel)
theorem bigint_return_normalized_protocol_preparation (kind : Fin 4) :
    UnifiedReduced.Caller.PreparedBoundaryExecution (normalizeData kind) (normalizeBefore kind) cells 16 12
      (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (normalizeAccepted kind) (normalizeInputs kind)
    (.bigintReturn (normalizeScope kind)) (normalizeLastScope kind) (by decide) (by decide +kernel) (by decide)

theorem bigint_return_normalized_actual (kind : Fin 4) :
    ∃ (seeds finishTokens : List (MemoryToken babyBearModulus)) (earlier current : List MemoryAccess) (start finish : State),
      earlier.Perm (((normalizeData kind).prefixSteps 8).map transferEvent) ∧
      current.Perm (((normalizeData kind).windowSteps 8 16).map transferEvent) ∧
      SailHistory cells earlier (normalizeBefore kind) start ∧ SailHistory cells current start finish ∧
      (Cell.register 12).read (normalizeBefore kind) =
        .ok (if kind = 0 then 128 else if kind = 1 then 192 else if kind = 2 then 0 else 65537) (normalizeBefore kind) ∧
      (Cell.register 12).read start = .ok (if kind = 1 then 1 else 0) start ∧
      (Cell.register 12).read finish = .ok 128 finish ∧
      (⟨(Cell.register 12).addressCode, (7, 0), Nat.pair (if kind = 1 then 1 else 0) 0⟩ : MemoryToken babyBearModulus) ∈ seeds ∧
      (⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩ : MemoryToken babyBearModulus) ∈ finishTokens := by
  obtain ⟨seeds, finishTokens, earlier, current, start, finish, earlierPerm, currentPerm,
    earlierHistory, currentHistory, prefixMatching, matching, startBoundary, finishBoundary⟩ :=
    (UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 8) (upper := 16)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (normalizeAccepted kind) (normalizeInputs kind)
      (by decide) (by decide) (by decide) (by decide)).execution
  let source : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (7, 0), Nat.pair (if kind = 1 then 1 else 0) 0⟩
  have sourceProduced : source ∈ (normalizeData kind).machine.initialMemory ++ ((normalizeData kind).prefixSteps 8).map Prod.snd := by
    fin_cases kind <;> decide +kernel
  have sourceNotRead : source ∉ ((normalizeData kind).prefixSteps 8).map Prod.fst := by fin_cases kind <;> decide +kernel
  have sourcePresent : source ∈ seeds := by
    rcases List.mem_append.mp (prefixMatching.mem_iff.mp sourceProduced) with present | read
    · exact present
    · exact False.elim (sourceNotRead read)
  let output : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩
  have outputProduced : output ∈ seeds ++ ((normalizeData kind).windowSteps 8 16).map Prod.snd := by
    apply List.mem_append.mpr; right
    fin_cases kind <;> decide +kernel
  have outputNotRead : output ∉ ((normalizeData kind).windowSteps 8 16).map Prod.fst := by fin_cases kind <;> decide +kernel
  have outputPresent : output ∈ finishTokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp outputProduced) with present | read
    · exact present
    · exact False.elim (outputNotRead read)
  obtain ⟨cell, _, code, sourceRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read startBoundary sourcePresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, outputRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read finishBoundary outputPresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  have sourceWord : source.word.toBitVec = (if kind = 1 then (1 : BitVec 32) else 0) := by fin_cases kind <;> decide +kernel
  have outputWord : output.word.toBitVec = (128 : BitVec 32) := by decide +kernel
  rw [sourceWord] at sourceRead
  rw [outputWord] at outputRead
  refine ⟨seeds, finishTokens, earlier, current, start, finish, earlierPerm, currentPerm,
    earlierHistory, currentHistory, ?_, sourceRead, outputRead, sourcePresent, outputPresent⟩
  apply read_register
  fin_cases kind
  all_goals simp [normalizeBefore, normalizeSeedBefore, mixedBefore, returnCarryBefore, returnCarryBase,
    abiBefore, wordWriteState, Tests.DelegationOperationEffects.before, Tests.BigintMemory.before]

theorem bigint_return_normalizer_xori_rejected :
    ¬ UnifiedReduced.Caller.BigintReturnPreparation binaryData [binaryEntry] 12 12 := by
  intro scope
  have instruction := scope.atCut binaryEntry (List.mem_singleton_self _) rfl
  cases instruction

theorem bigint_return_xori_one_does_not_normalize : Verification.byteOperation 4 (1 : BitVec 32) 1 ≠ 1 := by decide +kernel

theorem bigint_return_normalized_incomplete_reference (kind : Fin 4) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (normalizeData kind) normalizeProgram ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  have empty : ((normalizeData kind).workers.windowRows 16 16).length = 0 := by fin_cases kind <;> decide +kernel
  rw [empty] at count
  contradiction

private def normalizeForgedAssignment (one : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 34 then 6 else normalizeAssignment one 0 column
private def normalizeForged (kind : Fin 4) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { normalizeData kind with machine := { (normalizeData kind).machine with
      rows := [normalizeRow kind 1, ⟨.machine, normalizeForgedAssignment (kind = 1)⟩, sharedCaller] } }
theorem bigint_return_normalized_forged_read_rejected (kind : Fin 4) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (normalizeForged kind) normalizeProgram := by
  intro accepted
  let token := readToken (normalizeForgedAssignment (kind = 1)) UnifiedReduced.importedConstraintsMemoryPorts[0]
  have member : token ∈ (normalizeForged kind).mixedSteps.map Prod.fst := by fin_cases kind <;> decide +kernel
  have absent : token ∉ (normalizeForged kind).machine.initialMemory ++ (normalizeForged kind).mixedSteps.map Prod.snd := by
    fin_cases kind <;> decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))
theorem bigint_return_normalized_forged_read_native (one : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (normalizeForgedAssignment one))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (normalizeBefore 0)) ++ UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  ·
    cases one
    all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, normalizeForgedAssignment, normalizeAssignment, Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
      | exact ⟨(0 : Fin 2097537), rfl⟩
      | (refine ⟨(1 : Fin 2097537), ?_⟩
         change _ = (UnifiedReduced.Setup.fixedRow (1 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
      | (refine ⟨(65793 : Fin 2097537), ?_⟩
         change _ = (UnifiedReduced.Setup.fixedRow (65793 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
      | (refine ⟨(65794 : Fin 2097537), ?_⟩
         change _ = (UnifiedReduced.Setup.fixedRow (65794 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
      | (refine ⟨(66050 : Fin 2097537), ?_⟩
         change _ = (UnifiedReduced.Setup.fixedRow (66050 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals cases one <;> decide +kernel

theorem bigint_gaps_admit_empty_hash_segmentation (kind : Fin 4) :
    UnifiedReduced.Caller.IssuedHashSegmentation (normalizeData kind) [] := by
  have context : UnifiedReduced.Caller.ProtocolContextInputs (normalizeData kind) (normalizeBefore kind) [0] [4, 8] cells normalizeProgram :=
    ⟨(normalizeInputs kind).publicProgram, (normalizeInputs kind).ordinaryProgram, (normalizeInputs kind).initialization,
      (normalizeInputs kind).distinct, (normalizeInputs kind).aligned, (normalizeInputs kind).setup, (normalizeInputs kind).tables⟩
  apply UnifiedReduced.Caller.hash_segmentation_soundness (cut := 4) (by decide +kernel) (by decide +kernel)
    (normalizeAccepted kind) context normalizeRegistry
  · intro _ member; cases member
  · trivial
  · intro entry member family
    have same := List.mem_singleton.mp member
    subst entry
    exact False.elim (family rfl)

/-- Public code-policy fixtures; no accepted-trace claim is made for this
    artificially repeated public terminal clock. Every occurrence must be covered. -/
theorem hash_segmentation_repeated_occurrence_rejected :
    ¬ UnifiedReduced.Caller.ProgramHashCallerCoverage repeatedRoundCodeData [⟨.blakeRound 0, 4, 8⟩] := by
  intro coverage
  obtain ⟨window, member, lower, upper, _⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
    (List.mem_singleton_self _) (by decide) 4294967300
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
  have same := List.mem_singleton.mp member
  subst window
  change 4294967300 < 8 at upper
  omega

theorem hash_segmentation_wrong_family_rejected :
    ¬ UnifiedReduced.Caller.ProgramHashCallerCoverage roundCodeData [⟨.keccak, 4, 8⟩] := by
  intro coverage
  obtain ⟨window, member, _, _, family⟩ := coverage (Tests.DelegationCaller.entry .blakeRound)
    (List.mem_singleton_self _) (by decide) 4 (by decide) (by decide) (by decide) (by decide +kernel)
  have same := List.mem_singleton.mp member
  subst window
  cases family

theorem hash_segmentation_overlap_rejected :
    ¬ UnifiedReduced.Caller.WindowsOrdered 4 [(4, 228), (8, 232)] := by
  simp [UnifiedReduced.Caller.WindowsOrdered]

private theorem memoryOrdinaryCycles [Sail.ArchSem.MemoryPlatform SailRV32.exception] (store : Bool)
    (effects : UnifiedReduced.Caller.MixedMemoryEffects (memoryData store) (memoryBefore store) cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm ((memoryData store).mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events (memoryBefore store) finalState) :
    ∀ row ∈ (memoryData store).machine.rows, row ∉ (memoryData store).callers →
      UnifiedReduced.Caller.OrdinaryCycle [memoryEntry store] cells events (memoryBefore store) finalState row := by
  intro row member noncaller
  rcases List.mem_cons.mp member with rfl | member
  · refine ⟨memoryEntry store, List.mem_singleton_self _, ?_, Airbender.WordMemory.execution (memoryView store), ?_, ?_⟩
    · cases store <;> decide +kernel
    · cases store <;> rfl
    · have domain : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address := by
        intro address member
        simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
        rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
        all_goals unfold OrdinaryWordAddress
        all_goals interval_cases i <;> decide +kernel
      have words : UnifiedReduced.WordMemory.WordMapping (memoryView store) memoryOutput (memoryAssignment store) := by
        constructor <;> cases store <;> decide +kernel
      exact UnifiedReduced.Caller.Proofs.mixed_ram_cycle_at (memoryAccepted store) (memoryInputs store)
        effects permutation order history (memoryConfiguration store) domain (memoryCode store).ram
        (input := memoryView store) (output := memoryOutput) (by cases store <;> decide)
        List.mem_cons_self words ⟨memoryEntry store, List.mem_cons_self,
          by cases store <;> decide +kernel, by cases store <;> rfl⟩
  · have same := List.mem_singleton.mp member
    subst row
    exact False.elim (noncaller (by cases store <;> exact List.mem_singleton_self _))

theorem copy_then_ram_mixed_cycles [Sail.ArchSem.MemoryPlatform SailRV32.exception] (store : Bool) :
    UnifiedReduced.Caller.MixedCycleEffects (memoryData store) [memoryEntry store] (memoryBefore store) cells := by
  have effects := UnifiedReduced.Caller.Proofs.mixed_memory_effects (memoryAccepted store) (memoryInputs store)
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  exact UnifiedReduced.Caller.Proofs.mixed_cycle_effects_at (memoryAccepted store) (memoryInputs store)
    effects permutation order history (memoryCode store)
    (memoryOrdinaryCycles store effects permutation order history) terminal

theorem invalid_bigint_mixed_cycles [Sail.ArchSem.MemoryPlatform SailRV32.exception] (highControl : Bool) :
    UnifiedReduced.Caller.MixedCycleEffects (abiData highControl) [] (abiBefore highControl) cells := by
  have effects := UnifiedReduced.Caller.Proofs.mixed_memory_effects (abiAccepted highControl) (abiInputs highControl)
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  apply UnifiedReduced.Caller.Proofs.mixed_cycle_effects_at (abiAccepted highControl) (abiInputs highControl)
    effects permutation order history (abiCode highControl) _ terminal
  intro row member noncaller
  have same := List.mem_singleton.mp member
  subst row
  exact False.elim (noncaller (by cases highControl <;> exact List.mem_singleton_self _))

theorem invalid_bigint_padding_boundary (highControl : Bool) :
    UnifiedReduced.Caller.Padding.AcceptedLayout (abiData highControl) [] ∧
    UnifiedReduced.Caller.Padding.active (abiData highControl) = abiData highControl :=
  ⟨UnifiedReduced.Caller.Padding.Proofs.layout_of_accepted (abiAccepted highControl),
    UnifiedReduced.Caller.Padding.Proofs.active_of_accepted (abiAccepted highControl)⟩

theorem mixed_worker_rom_transport (store : Bool) :
    ExternalBoundary.WorkerRAM.Binding (memoryData store).workers.rows ∧
    UnifiedReduced.Caller.MixedMemoryAccepted
      (UnifiedReduced.Caller.NativeROM.view (memoryBefore store) (memoryData store)) [memoryEntry store] := by
  have ram := UnifiedReduced.Caller.NativeROM.ram_binding_soundness
    (memoryAccepted store) (memoryInputs store) (memoryCode store).ram
  exact ⟨ram, UnifiedReduced.Caller.NativeROM.acceptance_soundness (by decide)
    (memoryBefore store) (memoryAccepted store) ram⟩

theorem rom_interpretation_keeps_worker_requests (store : Bool) :
    (UnifiedReduced.Caller.NativeROM.view (memoryBefore store) (memoryData store)).calls =
      (memoryData store).calls ∧
    (UnifiedReduced.Caller.NativeROM.view (memoryBefore store) (memoryData store)).workers =
      (memoryData store).workers :=
  ⟨UnifiedReduced.Caller.NativeROM.Proofs.calls _ _, rfl⟩

private theorem copyCommands (store : Bool) : UnifiedReduced.Caller.BigintCommands (memoryData store) := by
  intro actual present _
  have same : actual = worker := List.mem_singleton.mp present
  subst actual
  refine ⟨⟨6, false⟩, ?_⟩
  unfold ExternalBoundary.BigintABI.Binding
  rw [ExternalBoundary.BigintABI.Proofs.input_word]
  decide +kernel

theorem copy_then_ram_full_reference [Sail.ArchSem.MemoryPlatform SailRV32.exception] (store : Bool) :
    ∃ events finalState, events.Perm ((memoryData store).mixedSteps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory cells events (memoryBefore store) finalState ∧
      UnifiedReduced.Caller.BigintCallCycle (memoryData store) (memoryBefore store) finalState cells events sharedCaller ∧
      UnifiedReduced.Caller.OrdinaryCycle [memoryEntry store] cells events (memoryBefore store) finalState (memoryRow store) := by
  obtain ⟨events, finalState, permutation, order, history, _, ordinary, _⟩ :=
    (copy_then_ram_mixed_cycles store).execution
  have reference := UnifiedReduced.Caller.bigint_call_soundness (memoryAccepted store) (memoryInputs store)
    (memoryCode store) (copyCommands store) permutation order history sharedCaller
    (by cases store <;> exact List.mem_singleton_self _) (by decide +kernel)
  have noncaller : memoryRow store ∉ (memoryData store).callers := by
    intro present
    have selected := of_decide_eq_true (List.mem_filter.mp present).2
    change memoryAssignment store 18 = 1 at selected
    cases store <;> norm_num [memoryAssignment, arithmetic] at selected
  exact ⟨events, finalState, permutation, order, history, reference,
    ordinary (memoryRow store) List.mem_cons_self noncaller⟩

/-- The real COPY then LW/SW fixture executes from its original public state,
    including an initial nextPC of 123, through full CSR and ordinary retirement. -/
theorem copy_then_ram_full_execution [Sail.ArchSem.MemoryPlatform SailRV32.exception] (store : Bool) :
    Realizes (UnifiedReduced.Caller.FullStep [memoryEntry store] (memoryData store).program)
      (memoryData store).machine (memoryBefore store) cells := by
  have effects := UnifiedReduced.Caller.Proofs.mixed_memory_effects (memoryAccepted store) (memoryInputs store)
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  have ledger : ExternalBoundary.Requests.Binding (memoryData store) := by
    cases store
    all_goals change [UnifiedReduced.Caller.request sharedAssignment].Perm [Delegation.Requests.fulfillment worker]
    all_goals decide +kernel
  have scopes : ∀ window ∈ ([] : List UnifiedReduced.Caller.HashWindow),
      UnifiedReduced.Caller.ComputedProtocolWindowInputs (memoryData store) [memoryEntry store] window := by simp
  have aligned : ∀ window ∈ ([] : List UnifiedReduced.Caller.HashWindow),
      window.lower % 4 = 0 ∧ window.upper % 4 = 0 := by simp
  have coverage : ∀ actual ∈ (memoryData store).workers.rows, actual.family ≠ .bigint →
      Delegation.Requests.Live (Delegation.Requests.fulfillment actual) →
      ∃ window ∈ ([] : List UnifiedReduced.Caller.HashWindow),
        actual ∈ (memoryData store).workers.windowRows window.lower window.upper := by
    intro actual present different _
    have same : actual = worker := List.mem_singleton.mp present
    subst actual
    exact False.elim (different rfl)
  exact UnifiedReduced.Caller.Proofs.full_execution_at (memoryAccepted store) (memoryInputs store) (memoryCode store)
    effects.requests (by
      have native : (memoryData store).machine.initial.word.toBitVec = 0 := by
        change sharedCaller.start.word.toBitVec = 0
        decide +kernel
      rw [native]
      apply read_register
      simp [memoryBefore, Std.ExtDHashMap.get?_insert]) ledger
    permutation order history (memoryOrdinaryCycles store effects permutation order history)
    (fun row member => UnifiedReduced.Caller.Proofs.full_caller_cycle_at (memoryAccepted store) (memoryInputs store)
      (memoryCode store) (copyCommands store) scopes aligned coverage effects permutation order history member)
    terminal

theorem invalid_bigint_full_reference_rejected (highControl : Bool) (after : State) :
    ¬ Bigint.Call.Executes (abiBefore highControl) after := by
  intro execution
  obtain ⟨control, read, positive, bound⟩ := Bigint.Call.Proofs.executes_control_range execution
  have actual : (Cell.register 12).read (abiBefore highControl) =
      .ok (if highControl then 65537 else 0) (abiBefore highControl) := by
    change run (SailRV32.readReg .x12) _ = _
    apply read_register
    simp [abiBefore, wordWriteState]
  have same := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  cases highControl
  · have zero : control = 0 := same
    rw [zero] at positive
    exact (Nat.not_lt_zero _) positive
  · have large : control = 65537 := same
    rw [large] at bound
    exact (by decide : ¬ (65537 : BitVec 32).toNat < 256) bound

end Tests.UnifiedDelegation
