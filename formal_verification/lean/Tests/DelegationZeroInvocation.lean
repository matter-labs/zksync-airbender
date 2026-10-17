import Airbender.Review.Circuits.AddSub.CallerTheorems
import Airbender.Review.Trace.Delegation.CallerTheorems
import Airbender.Review.Trace.UnifiedReduced.Theorems
import Airbender.Review.Trace.Padding
import Airbender.Proofs.Blake2G.Claims
import Airbender.Proofs.Delegation.Requests
import Airbender.Proofs.Sail.WordMemoryState
import Mathlib.Tactic.IntervalCases
import Tests.DelegationCaller
import Airbender.Proofs.Trace.ImageFrame

namespace Tests.DelegationZeroInvocation
open Airbender Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def row (column : Nat) : ZMod babyBearModulus :=
  if column = 0 ∨ column = 5 ∨ column = 12 then 1
  else if column = 8 then 4
  else if column = 9 then 8
  else if column = 10 then 12
  else if column = 14 ∨ column = 31 ∨ column = 32 then 64
  else if 83 ≤ column ∧ column < 110 ∧ (column - 83) % 3 = 2 then 1
  else 0

private abbrev table : Table (ZMod babyBearModulus) (fields 9) :=
  Blake2G.setupTable Blake2G.Control.controllerRows

private def indices : Vector Nat 19 :=
  #v[344640, 0, 0, 0, 0, 65536, 82240, 65600, 65536, 82240, 65600,
    0, 0, 0, 0, 65856, 82240, 65856, 82240]

private theorem indexBound (i : Fin 19) : indices[i] < 344896 := by
  fin_cases i <;> decide

private theorem tableQuery (i : Fin 19) :
    ((FlatOperation.lookups (Blake2G.importedConstraints table)).get
      ⟨i.val + 2, by rw [Blake2G.lookup_count]; omega⟩).Contains (Verification.environment row) := by
  let index : Fin 344896 := ⟨indices[i], indexBound i⟩
  fin_cases i
  all_goals refine ⟨index, ?_⟩
  all_goals simp only [Blake2G.Proofs.setup_row_characterization]
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals change j < 9 at hj
  all_goals interval_cases j
  all_goals simp only [Vector.getElem_map]
  all_goals decide +kernel +revert

private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2G.importedConstraints table) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 21 := by simpa only [Blake2G.lookup_count] using hi
    by_cases small : i < 2
    · interval_cases i
      all_goals apply Verification.range16_contains
      all_goals decide
    · have source := tableQuery ⟨i - 2, by omega⟩
      have position : i - 2 + 2 = i := by omega
      simpa only [List.get_eq_getElem, Fin.val_mk, position] using source

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2G.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 20 := by simpa only [Blake2G.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Blake2G.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, row, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

private def native : Delegation.Row babyBearModulus := ⟨.blakeG, row⟩
private def setup : Delegation.Setup babyBearModulus :=
  Delegation.modeledSetup (fun _ => Vector.replicate 6 0)
private def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd
private def cells : List Cell :=
  [.register 10, .ram 4194304, .ram 4194320, .ram 4194336, .ram 4194352,
    .register 11, .ram 4194368, .ram 4194372, .register 12]
private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x10 (4194304 : BitVec 32)
    |>.insert .x11 (4194368 : BitVec 32) |>.insert .x12 (0 : BitVec 32)
  mem := (Std.ExtHashMap.emptyWithCapacity)
    |>.insert 4194304 (0 : BitVec 8)
    |>.insert 4194305 (0 : BitVec 8)
    |>.insert 4194306 (0 : BitVec 8)
    |>.insert 4194307 (0 : BitVec 8)
    |>.insert 4194320 (0 : BitVec 8)
    |>.insert 4194321 (0 : BitVec 8)
    |>.insert 4194322 (0 : BitVec 8)
    |>.insert 4194323 (0 : BitVec 8)
    |>.insert 4194336 (0 : BitVec 8)
    |>.insert 4194337 (0 : BitVec 8)
    |>.insert 4194338 (0 : BitVec 8)
    |>.insert 4194339 (0 : BitVec 8)
    |>.insert 4194352 (0 : BitVec 8)
    |>.insert 4194353 (0 : BitVec 8)
    |>.insert 4194354 (0 : BitVec 8)
    |>.insert 4194355 (0 : BitVec 8)
    |>.insert 4194368 (0 : BitVec 8)
    |>.insert 4194369 (0 : BitVec 8)
    |>.insert 4194370 (0 : BitVec 8)
    |>.insert 4194371 (0 : BitVec 8)
    |>.insert 4194372 (0 : BitVec 8)
    |>.insert 4194373 (0 : BitVec 8)
    |>.insert 4194374 (0 : BitVec 8)
    |>.insert 4194375 (0 : BitVec 8)
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

private theorem initialized : initialImage before cells = some data.initial := by
  have x10 : Cell.read (.register 10) before = .ok 4194304 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) before = .ok 4194368 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x12 : Cell.read (.register 12) before = .ok 0 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert,
    Cell.initialToken, data, native, Delegation.Row.memorySteps, Delegation.Row.ports,
    Blake2G.importedConstraintsMemoryPorts, readToken, MemoryAddress.code,
    Verification.IndirectPort.rawAddress, MemoryPort.readCode, WordColumns.code,
    WordColumns.evaluate, rawPair, row, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
  all_goals decide

private def input : Blake2G.Input := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
private def output : Blake2G.Words := ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

private theorem interface : Blake2G.Memory.InterfaceAssumptions data before cells input output row := by
  constructor
  · exact accepted
  · constructor
    · exact initialized
    · decide
    · intro actual member
      simp only [data, List.mem_singleton] at member
      subst actual
      decide
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    rfl
  · rfl

theorem native_soundness : Blake2G.spec input output := by
  apply Blake2G.Memory.babyBear_soundness data before cells input output row
  refine ⟨interface, Verification.holds_append core clocks, ?_⟩
  constructor
  · constructor <;> rfl
  · exact List.mem_singleton_self _

theorem native_operation_execution : Delegation.MemoryExecution data before cells ∧
    Blake2G.spec (Blake2G.Native.input row) (Blake2G.Native.output row) := by
  have operationInputs : Delegation.OperationInputs data before cells (fun _ => Vector.replicate 6 0) := by
    refine ⟨interface.publicState, rfl, ?_, ?_⟩
    · intro actual member family
      simp only [data, List.mem_singleton] at member
      subst actual
      cases family
    · intro actual member family
      simp only [data, List.mem_singleton] at member
      subst actual
      cases family
  have aligned : ∀ cell ∈ cells, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  have result := Blake2G.Native.operation_execution (by decide) (by decide) accepted operationInputs aligned
  exact ⟨result.1, result.2 native (by simp [data]) rfl⟩


theorem active_zero_invocation : row Blake2G.Variables.execute = 1 ∧
    (Delegation.Requests.fulfillment native).time = (0, 0) := by
  decide +kernel

theorem no_caller_virtual_matching :
    Delegation.Requests.Matching [] [Delegation.Requests.fulfillment native] := by
  exact Delegation.Requests.Proofs.zero_time_fulfillment_invisible _

private def sharedWorkers : Delegation.MemoryData babyBearModulus where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := [native]
  initial := data.initial
  terminal := data.terminal
private def sharedMachine : PooledTrace babyBearModulus where
  rows := []
  rom := ⟨{ name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩
  initial := ⟨(0, 0), (4, 0)⟩
  terminal := ⟨(0, 0), (4, 0)⟩
  initialMemory := data.initial
  terminalMemory := data.terminal
private def sharedData : Delegation.Caller.RequestTrace babyBearModulus :=
  ⟨sharedMachine, sharedWorkers, []⟩

private theorem sharedAccepted : Delegation.Caller.SharedMemoryAccepted sharedData := by
  refine ⟨?_, rfl, accepted.matching⟩
  constructor
  · intro _ member; cases member
  · intro _ member; cases member
  · exact List.Perm.refl _
  · intro _ member; cases member
  · intro actual member
    have same : actual = native := List.mem_singleton.mp member
    subst actual
    exact Verification.holds_append core clocks
  · intro actual member
    have same : actual = native := List.mem_singleton.mp member
    subst actual
    exact active_zero_invocation.1
  · exact no_caller_virtual_matching

private theorem sharedInputs : Delegation.Caller.SharedOperationInputs sharedData before [] cells := by
  refine ⟨?_, rfl, ?_⟩
  · refine ⟨⟨rfl, ?_, rfl⟩, initialized, by decide, ?_⟩
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · intro cell member
      simp [cells] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [Cell.Aligned]
  · intro actual member family
    have same : actual = native := List.mem_singleton.mp member
    subst actual
    cases family

theorem shared_unissued_worker_accepted : Delegation.Caller.SharedOperationEffects sharedData before cells :=
  Delegation.Caller.shared_operation_soundness sharedAccepted sharedInputs

theorem shared_unissued_control_update : ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    sharedData.calls = [] ∧ events.Perm (sharedData.sharedSteps.map transferEvent) ∧
    Trace.SailHistory cells events before after ∧
    (Cell.register 12).read before = .ok 0 before ∧
    (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨events, after, permutation, _, history, terminal⟩ := shared_unissued_worker_accepted.memory.execution
  let port := native.ports[8]
  let sink := native.writeToken port
  have member : sink ∈ sharedData.machine.terminalMemory := by
    apply List.mem_map.mpr
    refine ⟨(readToken row port, sink), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨port, by simp [port, native, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts], rfl⟩
  obtain ⟨cell, _, same, read⟩ := terminal sink member
  have address : sink.address = (Cell.register 12).addressCode := by decide +kernel
  have equal := Trace.Proofs.cell_address_injective (same.trans address)
  subst cell
  refine ⟨events, after, rfl, permutation, history, ?_, ?_⟩
  · apply Reference.RiscV.Sail.read_register
    simp [before]
  · have value : sink.word.toBitVec = (1 : BitVec 32) := by decide +kernel
    simpa only [value] using read

private def mixedData : Delegation.Caller.RequestTrace babyBearModulus :=
  { sharedData with machine := { sharedMachine with rom :=
    ⟨ROM.table cells sharedMachine.initialMemory, Verification.subwordTable (ROM.words before)⟩ } }

private theorem mixedAccepted : Delegation.Caller.MixedMemoryAccepted mixedData [] := by
  refine ⟨?_, ?_, accepted.matching⟩
  · constructor
    · intro _ member; cases member
    · intro _ member; cases member
    · exact sharedAccepted.states
    · exact sharedAccepted.decoded
    · exact sharedAccepted.workerConstraints
    · exact sharedAccepted.workerActive
    · exact sharedAccepted.requests
  · intro _ member; cases member

private theorem mixedInputs : Delegation.Caller.MixedMemoryInputs mixedData [] before [] [] cells :=
  ⟨⟨⟨sharedInputs.publicProgram.image, sharedInputs.publicProgram.initialClock,
      sharedInputs.publicProgram.initialAligned⟩, sharedInputs.initialization,
    sharedInputs.distinct, sharedInputs.aligned⟩, rfl, rfl, rfl, rfl, sharedInputs.rounds⟩

theorem mixed_unissued_worker_accepted : Delegation.Caller.MixedMemoryEffects mixedData before cells :=
  Delegation.Caller.mixed_memory_soundness mixedAccepted mixedInputs

theorem mixed_unissued_control_update : ∃ after : Reference.RiscV.Sail.State,
    mixedData.calls = [] ∧ (Cell.register 12).read before = .ok 0 before ∧
    (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨_, after, _, _, _, terminal⟩ := mixed_unissued_worker_accepted.execution
  let port := native.ports[8]
  let sink := native.writeToken port
  have member : sink ∈ mixedData.machine.terminalMemory := by
    apply List.mem_map.mpr
    refine ⟨(readToken row port, sink), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨port, by simp [port, native, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts], rfl⟩
  obtain ⟨cell, _, same, read⟩ := terminal sink member
  have address : sink.address = (Cell.register 12).addressCode := by decide +kernel
  have equal := Trace.Proofs.cell_address_injective (same.trans address)
  subst cell
  refine ⟨after, rfl, ?_, ?_⟩
  · apply Reference.RiscV.Sail.read_register
    simp [before]
  · have value : sink.word.toBitVec = (1 : BitVec 32) := by decide +kernel
    simpa only [value] using read

theorem zero_worker_has_no_scheduled_caller :
    ¬ ∃ caller ∈ mixedData.callers, Delegation.Requests.fulfillment native = Delegation.Requests.caller caller.assignment := by
  have schedule := Delegation.Caller.worker_schedule_soundness
    (by norm_num [timestampBase, babyBearModulus]) (by decide +kernel) (by decide +kernel)
    mixedAccepted.toRequestChecks mixedInputs.publicProgram
  exact (schedule.unissued native (by simp [mixedData, sharedData, sharedWorkers])).mpr (by decide +kernel)

theorem zero_worker_retained_before_request_window :
    Delegation.Caller.RequestWindowBinding mixedData.callers mixedData.workers 4 8 ∧
    mixedData.workers.prefixRows 4 = [native] ∧ mixedData.workers.windowRows 4 8 = [] ∧
    ∃ after : Reference.RiscV.Sail.State,
      (Cell.register 12).read before = .ok 0 before ∧
      (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨after, _, initial, terminal⟩ := mixed_unissued_control_update
  refine ⟨Delegation.Caller.request_window_soundness
    (by norm_num [timestampBase, babyBearModulus]) (by decide +kernel) (by decide +kernel)
    mixedAccepted.toRequestChecks mixedInputs.publicProgram (by decide) (by decide) (by decide),
    ?_, ?_, after, initial, terminal⟩
  · change ([native].filter fun worker => decide (worker.writeTime ≤ 4)) = [native]
    have time : native.writeTime = 2 := by decide +kernel
    simp [time]
  · change ([native].filter fun worker => decide (4 < worker.writeTime ∧ worker.writeTime ≤ 8)) = []
    have time : native.writeTime = 2 := by decide +kernel
    simp [time]

private def unifiedData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := []
    rom := UnifiedReduced.Setup.table before
    initial := sharedMachine.initial
    terminal := sharedMachine.terminal
    initialMemory := data.initial
    terminalMemory := data.terminal }
  workers := sharedWorkers
  program := []

private theorem unifiedAccepted : UnifiedReduced.Caller.MixedMemoryAccepted unifiedData [] := by
  refine ⟨?_, ?_, accepted.matching⟩
  constructor
  · intro _ member; cases member
  · intro _ member; cases member
  · exact List.Perm.refl _
  · intro _ member; cases member
  · exact sharedAccepted.workerConstraints
  · exact sharedAccepted.workerActive
  · exact no_caller_virtual_matching
  · intro _ member; cases member

private theorem unifiedInputs : UnifiedReduced.Caller.MixedMemoryInputs unifiedData [] before [] [] cells := by
  refine ⟨⟨rfl, sharedInputs.publicProgram.initialClock, sharedInputs.publicProgram.initialAligned⟩,
    rfl, sharedInputs.initialization, sharedInputs.distinct, sharedInputs.aligned, rfl, rfl, ?_⟩
  intro actual member family
  have same : actual = native := List.mem_singleton.mp member
  subst actual
  cases family

private theorem unifiedCode : UnifiedReduced.Caller.CodeProfile unifiedData [] cells := by
  constructor
  · intro address member
    simp [cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide +kernel
  · intro _ member; cases member
  · intro _ member; cases member

theorem unified_unissued_worker_caller_cycles :
    UnifiedReduced.Caller.CallerCycleEffects unifiedData [] before cells :=
  UnifiedReduced.Caller.caller_cycles_soundness unifiedAccepted unifiedInputs unifiedCode (by decide +kernel)

theorem unified_unissued_control_update : ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    unifiedData.callers = [] ∧ events.Perm (unifiedData.mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events before after ∧
    (Cell.register 12).read before = .ok 0 before ∧ (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨events, after, permutation, _, history, _, _, terminal⟩ := unified_unissued_worker_caller_cycles.execution
  let port := native.ports[8]
  let sink := native.writeToken port
  have member : sink ∈ unifiedData.machine.terminalMemory := by
    change sink ∈ native.memorySteps.map Prod.snd
    simp only [Delegation.Row.memorySteps, List.map_map, Function.comp_def]
    apply List.mem_map.mpr
    exact ⟨port, by simp [port, native, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts], rfl⟩
  obtain ⟨cell, _, address, read⟩ := terminal sink member
  have code : sink.address = (Cell.register 12).addressCode := by decide +kernel
  have same := Trace.Proofs.cell_address_injective (address.trans code)
  subst cell
  refine ⟨events, after, rfl, permutation, history, ?_, ?_⟩
  · apply Reference.RiscV.Sail.read_register
    simp [before]
  · have value : sink.word.toBitVec = (1 : BitVec 32) := by decide +kernel
    simpa only [value] using read

private def preparationAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 30 ∨ column = 40 then 4
  else if column = 32 then 8
  else if column = 7 ∨ column = 44 then 12
  else if column = 46 then 2
  else if column = 4 ∨ column = 11 ∨ column = 48 ∨
      column = 129 ∨ column = 130 ∨ column = 131 ∨ column = 132 ∨ column = 133 then 1
  else 0
private def preparationRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, preparationAssignment⟩
private def preparationBefore : Reference.RiscV.Sail.State :=
  Reference.RiscV.Sail.wordWriteState before 0 0x00000613
private def preparationCells : List Cell := .register 0 :: cells
private def preparationEntry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0x00000613, (UnifiedReduced.Caller.ControlLiteral.addi 0).instruction 12,
    ⟨.machine, 0, 0, 12, ⟨0, 0⟩, 1, 0⟩⟩
private def preparationData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [preparationRow]
    rom := UnifiedReduced.Setup.table preparationBefore
    initial := preparationRow.start
    terminal := preparationRow.finish
    initialMemory := (Cell.register 0).initialToken 0 :: data.initial
    terminalMemory := ⟨(Cell.register 0).addressCode, (5, 0), 0⟩ ::
      ⟨(Cell.register 12).addressCode, (6, 0), 0⟩ ::
      data.terminal.filter (fun token => token.address != (Cell.register 12).addressCode) }
  workers := sharedWorkers
  program := []

private theorem preparationCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment preparationAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table preparationBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, preparationAssignment, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (with_unfolding_all refine ⟨⟨0, by decide⟩, ?_⟩
       dsimp only
       rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
       simp only [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
         UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
       with_unfolding_all decide +kernel)
    | decide +kernel

private theorem preparationClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment preparationAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem preparationAccepted :
    UnifiedReduced.Caller.MixedMemoryAccepted preparationData [preparationEntry] := by
  constructor
  · constructor
    · intro current member
      have same : current = preparationRow := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append preparationCore preparationClocks
    · intro current member
      have same : current = preparationRow := List.mem_singleton.mp member
      subst current
      rfl
    · exact List.Perm.swap _ _ []
    · intro current member
      have empty : preparationData.callers = [] := by decide +kernel
      rw [empty] at member
      cases member
    · exact sharedAccepted.workerConstraints
    · exact sharedAccepted.workerActive
    · exact no_caller_virtual_matching
  · intro current member _
    have same : current = preparationRow := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, preparationRow.decoderQuery = ([preparationEntry].get i).query
    exact ⟨0, by decide +kernel⟩
  · decide +kernel

private theorem preparationProgram :
    UnifiedReduced.Mixed.programImage preparationBefore [0] = some [preparationEntry] := by
  have bytes : (Cell.ram 0).read preparationBefore = .ok 0x00000613 preparationBefore :=
    Reference.RiscV.Sail.written_word_read before 0 _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x00000613) preparationBefore =
      .ok preparationEntry.instruction preparationBefore := by with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields preparationEntry.instruction = some preparationEntry.data := by
    with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem preparationImage :
    initialImage preparationBefore preparationCells = some preparationData.machine.initialMemory := by
  have x10 : Cell.read (.register 10) preparationBefore = .ok 4194304 preparationBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [preparationBefore, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) preparationBefore = .ok 4194368 preparationBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [preparationBefore, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  have x12 : Cell.read (.register 12) preparationBefore = .ok 0 preparationBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [preparationBefore, Reference.RiscV.Sail.wordWriteState, before]
  have zero : Cell.read (.register 0) preparationBefore = .ok 0 preparationBefore := rfl
  simp only [initialImage, preparationCells, cells, List.mapM_cons, List.mapM_nil, zero, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, preparationBefore, Reference.RiscV.Sail.wordWriteState,
    before, Std.ExtHashMap.getElem_insert, Cell.initialToken, preparationData, data, native,
    Delegation.Row.memorySteps, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, row, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
  all_goals decide +kernel

private theorem preparationInputs :
    UnifiedReduced.Caller.MixedMemoryInputs preparationData [preparationEntry] preparationBefore [] [0] preparationCells := by
  refine ⟨⟨rfl, ?_, by decide⟩, preparationProgram, preparationImage, by decide, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · intro cell member
    simp [preparationCells, cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  · intro current member family
    have same : current = native := List.mem_singleton.mp member
    subst current
    cases family

theorem control_preparation_after_unissued_worker :
    preparationData.workers.prefixRows 8 = [native] ∧
      UnifiedReduced.Caller.PreparedBoundaryExecution preparationData preparationBefore preparationCells 8 12 (.addi 0) := by
  have time : native.writeTime = 2 := by decide +kernel
  refine ⟨?_, ?_⟩
  · change ([native].filter fun worker => decide (worker.writeTime ≤ 8)) = [native]
    simp [time]
  · apply UnifiedReduced.Caller.control_preparation_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
      preparationAccepted preparationInputs _ (by decide) (by decide)
    refine ⟨?_, ?_, by decide +kernel, by decide +kernel⟩
    · apply UnifiedReduced.Caller.PreparationProgram.uniform
      intro entry member
      have same : entry = preparationEntry := List.mem_singleton.mp member
      subst entry
      rfl
    · change ([native].filter fun worker => decide (4 < worker.writeTime ∧ worker.writeTime ≤ 8)) = []
      simp [time]

theorem preparation_reads_unissued_control_update :
    (readToken preparationAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (2, 0) ∧
      (readToken preparationAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = 1 ∧
      (writeToken preparationRow.columns preparationAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
      (writeToken preparationRow.columns preparationAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = 0 := by
  decide +kernel

private def fabricatedPreparationAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 48 then 0 else preparationAssignment column
private def fabricatedPreparationData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { preparationData with machine := { preparationData.machine with
    rows := [⟨.machine, fabricatedPreparationAssignment⟩] } }

theorem fabricated_preparation_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted fabricatedPreparationData [preparationEntry] := by
  intro accepted
  let token := readToken fabricatedPreparationAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]
  have consumed : token ∈ fabricatedPreparationData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ fabricatedPreparationData.machine.initialMemory ++
      fabricatedPreparationData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append_right _ consumed))

theorem chain_retains_unissued_prefix_effect :
    ∃ chain : UnifiedReduced.Caller.WindowChain babyBearModulus,
      chain.Realizes preparationData preparationBefore preparationCells 4 4 4 8 ∧
      (Cell.register 12).read chain.atFirstStart = .ok 1 chain.atFirstStart ∧
      (Cell.register 12).read chain.atSecondFinish = .ok 0 chain.atSecondFinish := by
  obtain ⟨chain, history⟩ := UnifiedReduced.Caller.mixed_window_chain_soundness
    (a := 4) (b := 4) (c := 4) (d := 8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) preparationAccepted preparationInputs
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (2, 0), Nat.pair 1 0⟩
  have produced : token ∈ preparationData.machine.initialMemory ++ (preparationData.prefixSteps 4).map Prod.snd := by decide +kernel
  have notRead : token ∉ (preparationData.prefixSteps 4).map Prod.fst := by decide +kernel
  have present : token ∈ chain.firstStart := by
    rcases List.mem_append.mp (history.firstPrefixMatching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  obtain ⟨cell, _, address, firstRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read history.firstStartBoundary present
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have matching := UnifiedReduced.Caller.Proofs.matching_at_next_cut (by decide +kernel) (by decide +kernel)
    (lower := 4) (upper := 8) preparationAccepted.toRequestChecks preparationInputs.publicProgram
    (by decide) (by decide) (by decide) (by decide)
    history.secondPrefixMatching history.secondMatching
  have scope : UnifiedReduced.Caller.ControlPreparation preparationData [preparationEntry] 8 12 (.addi 0) := by
    refine ⟨.uniform ?_, ?_, by decide +kernel, by decide +kernel⟩
    · intro entry member
      have same : entry = preparationEntry := List.mem_singleton.mp member
      subst entry
      rfl
    · have time : native.writeTime = 2 := by decide +kernel
      change ([native].filter fun worker => decide (4 < worker.writeTime ∧ worker.writeTime ≤ 8)) = []
      simp [time]
  have lastRead := UnifiedReduced.Caller.Proofs.preparation_at_boundary (by decide +kernel) (by decide +kernel)
    preparationAccepted preparationInputs scope (by decide) (by decide) matching history.secondFinishBoundary
  have bits : token.word.toBitVec = (1 : BitVec 32) := by
    simp only [token, MemoryToken.word, Nat.unpair_pair]
    rfl
  rw [bits] at firstRead
  exact ⟨chain, history, firstRead, lastRead.1⟩

theorem sequence_retains_unissued_prefix_effect :
    ∃ sequence : UnifiedReduced.Caller.WindowSequence babyBearModulus,
      sequence.Realizes preparationData preparationBefore preparationCells 4 [(4, 4), (4, 4), (4, 8)] ∧
      (Cell.register 12).read sequence.atInitial = .ok 1 sequence.atInitial := by
  obtain ⟨sequence, history⟩ := UnifiedReduced.Caller.mixed_window_sequence_soundness
    (cut := 4) (windows := [(4, 4), (4, 4), (4, 8)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) preparationAccepted preparationInputs
    (by decide) (by decide) (by simp [UnifiedReduced.Caller.WindowsOrdered])
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (2, 0), Nat.pair 1 0⟩
  have produced : token ∈ preparationData.machine.initialMemory ++ (preparationData.prefixSteps 4).map Prod.snd := by decide +kernel
  have notRead : token ∉ (preparationData.prefixSteps 4).map Prod.fst := by decide +kernel
  have present : token ∈ sequence.initial := by
    rcases List.mem_append.mp (history.prefixMatching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  obtain ⟨cell, _, address, actualRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read history.boundary present
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have bits : token.word.toBitVec = (1 : BitVec 32) := by
    simp only [token, MemoryToken.word, Nat.unpair_pair]
    rfl
  rw [bits] at actualRead
  exact ⟨sequence, history, actualRead⟩

private theorem program_protocol_inputs_keep_unissued :
    UnifiedReduced.Caller.ProgramPreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] := by
  have context := preparationInputs
  refine ⟨⟨context.publicProgram, context.ordinaryProgram, context.initialization, context.distinct,
    context.aligned, context.setup, context.tables⟩, ?_, ?_, ?_⟩
  · intro entry member
    have same : entry = preparationEntry := List.mem_singleton.mp member
    subst entry
    exact .arithmetic (.addi 0 0 12)
  · intro region member
    cases member
  · intro row member same
    have only : row = native := List.mem_singleton.mp member
    subst row
    cases same

private theorem wrapped_program_inputs_keep_unissued :
    UnifiedReduced.Caller.WrappedProgramPreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] := by
  have old := program_protocol_inputs_keep_unissued
  refine ⟨old.toProtocolContextInputs, ⟨fun entry member => .sequential (old.registry entry member), ?_⟩,
    ?_, old.coverage⟩
  · intro entry member
    have same : entry = preparationEntry := List.mem_singleton.mp member
    subst entry
    decide +kernel
  · intro region member; cases member

private theorem prepared_protocol_inputs_keep_unissued :
    UnifiedReduced.Caller.PreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] :=
  UnifiedReduced.Caller.Proofs.wrapped_program_prepared_protocol_inputs (by decide +kernel) (by decide +kernel)
    preparationAccepted wrapped_program_inputs_keep_unissued

theorem wrapped_program_regions_admit_unissued_worker :
    UnifiedReduced.Caller.WrappedProgramPreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] ∧
    native ∈ preparationData.workers.rows ∧
    ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) :=
  ⟨wrapped_program_inputs_keep_unissued, List.mem_singleton_self _, by decide +kernel⟩

theorem program_regions_admit_unissued_worker :
    UnifiedReduced.Caller.ProgramPreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] ∧
    native ∈ preparationData.workers.rows ∧
    ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) :=
  ⟨program_protocol_inputs_keep_unissued, List.mem_singleton_self _, by decide +kernel⟩

theorem public_round_coverage_retains_unissued_g :
    UnifiedReduced.Caller.ProgramRoundCallerCoverage preparationData [] ∧
    UnifiedReduced.Caller.RoundWorkerCoverage preparationData [] ∧
    native ∈ preparationData.workers.rows ∧
    ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) := by
  have code : UnifiedReduced.Caller.ProgramRoundCallerCoverage preparationData [] := by
    intro entry member
    cases member
  have inputs := program_protocol_inputs_keep_unissued
  have covered := UnifiedReduced.Caller.program_round_coverage_soundness (by decide +kernel) (by decide +kernel)
    preparationAccepted inputs.publicProgram inputs.ordinaryProgram inputs.registry inputs.scopes code
  exact ⟨code, covered, List.mem_singleton_self _, by decide +kernel⟩

theorem wrapped_public_round_coverage_retains_unissued_g :
    UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage preparationData [] ∧
    UnifiedReduced.Caller.RoundWorkerCoverage preparationData [] ∧
    native ∈ preparationData.workers.rows ∧
    ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) := by
  have code : UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage preparationData [] := by
    intro entry member
    cases member
  have inputs := wrapped_program_inputs_keep_unissued
  have covered := UnifiedReduced.Caller.wrapped_program_round_coverage_soundness (by decide +kernel) (by decide +kernel)
    inputs.setup preparationAccepted inputs.publicProgram inputs.ordinaryProgram inputs.registry inputs.scopes code
  exact ⟨code, covered, List.mem_singleton_self _, by decide +kernel⟩

theorem prepared_regions_retain_unissued_prefix_effect :
    ∃ sequence : UnifiedReduced.Caller.WindowSequence babyBearModulus,
      sequence.Realizes preparationData preparationBefore preparationCells 4 [(4, 4), (4, 8)] ∧
      (Cell.register 12).read sequence.atInitial = .ok 1 sequence.atInitial := by
  have memory := UnifiedReduced.Caller.Proofs.prepared_protocol_memory_inputs (by decide +kernel) (by decide +kernel)
    preparationAccepted prepared_protocol_inputs_keep_unissued
  obtain ⟨sequence, history⟩ := UnifiedReduced.Caller.mixed_window_sequence_soundness
    (cut := 4) (windows := [(4, 4), (4, 8)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) preparationAccepted memory
    (by decide) (by decide) (by simp [UnifiedReduced.Caller.WindowsOrdered])
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (2, 0), Nat.pair 1 0⟩
  have produced : token ∈ preparationData.machine.initialMemory ++ (preparationData.prefixSteps 4).map Prod.snd := by decide +kernel
  have notRead : token ∉ (preparationData.prefixSteps 4).map Prod.fst := by decide +kernel
  have present : token ∈ sequence.initial := by
    rcases List.mem_append.mp (history.prefixMatching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  obtain ⟨cell, _, address, actualRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read history.boundary present
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have bits : token.word.toBitVec = (1 : BitVec 32) := by
    simp only [token, MemoryToken.word, Nat.unpair_pair]
    rfl
  rw [bits] at actualRead
  exact ⟨sequence, history, actualRead⟩

theorem unified_unissued_reads_public_initialization :
    UnifiedReduced.Caller.InitialWorkerReads before cells native :=
  UnifiedReduced.Caller.unissued_worker_reads_soundness (by decide +kernel) (by decide +kernel)
    unifiedAccepted unifiedInputs.publicProgram unifiedInputs.initialization
    (List.mem_singleton_self _) (by decide +kernel)

theorem prepared_unissued_reads_public_initialization :
    UnifiedReduced.Caller.InitialWorkerReads preparationBefore preparationCells native :=
  UnifiedReduced.Caller.unissued_worker_reads_soundness (by decide +kernel) (by decide +kernel)
    preparationAccepted preparationInputs.publicProgram preparationInputs.initialization
    (List.mem_singleton_self _) (by decide +kernel)

/-- The earlier G write and later ADDI reset both satisfy the derived write floor. -/
theorem prepared_unissued_write_floor :
    ∀ edge ∈ preparationData.mixedSteps, 2 ≤ (timeOfPair edge.2.time).value :=
  UnifiedReduced.Caller.Proofs.mixed_write_floor (by decide +kernel) (by decide +kernel)
    preparationAccepted preparationInputs.publicProgram preparationInputs.initialization

theorem unified_worker_invocations_include_zero :
    UnifiedReduced.Caller.WorkerInvocationUniqueness unifiedData :=
  UnifiedReduced.Caller.worker_invocation_uniqueness_soundness (by decide +kernel) (by decide +kernel)
    unifiedAccepted unifiedInputs.publicProgram unifiedInputs.initialization unifiedInputs.distinct

theorem prepared_worker_invocations_include_zero :
    UnifiedReduced.Caller.WorkerInvocationUniqueness preparationData :=
  UnifiedReduced.Caller.worker_invocation_uniqueness_soundness (by decide +kernel) (by decide +kernel)
    preparationAccepted preparationInputs.publicProgram preparationInputs.initialization preparationInputs.distinct

/-- The derived bound is attained by the existing state-changing G worker. -/
theorem unissued_worker_bound_is_sharp :
    UnifiedReduced.Caller.WorkerInvocationUniqueness preparationData ∧
    (preparationData.workers.rows.filter fun worker =>
      decide ((Delegation.Requests.fulfillment worker).time = (0, 0))).length = 1 :=
  ⟨prepared_worker_invocations_include_zero, by decide +kernel⟩

private def duplicateUnissuedData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { unifiedData with workers := { unifiedData.workers with rows := [native, native] } }

/-- Native rows, participation and virtual requests alone still admit two copies
    of the zero-clock G worker. Architectural matching supplies the missing limit. -/
theorem duplicate_unissued_request_checks : UnifiedReduced.Caller.RequestChecks duplicateUnissuedData := by
  constructor
  · intro row member; cases member
  · intro row member; cases member
  · exact List.Perm.refl _
  · intro row member; cases member
  · intro row member
    have same : row = native := by
      change row ∈ [native, native] at member
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member
    subst row
    exact unifiedAccepted.workerConstraints native (List.mem_singleton_self _)
  · intro row member
    have same : row = native := by
      change row ∈ [native, native] at member
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member
    subst row
    exact unifiedAccepted.workerActive native (List.mem_singleton_self _)
  · change [Delegation.Requests.Request.empty (Delegation.Requests.fulfillment native),
      Delegation.Requests.Request.empty (Delegation.Requests.fulfillment native)].Perm
      [Delegation.Requests.Request.issued (Delegation.Requests.fulfillment native),
        Delegation.Requests.Request.issued (Delegation.Requests.fulfillment native)]
    have zero : (Delegation.Requests.fulfillment native).time = (0, 0) := by decide +kernel
    simp only [Delegation.Requests.Request.issued, Delegation.Requests.Request.empty, zero]
    exact List.Perm.refl _

theorem duplicate_unissued_workers_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted duplicateUnissuedData [] := by
  intro accepted
  have inputs : UnifiedReduced.Caller.RequestInputs duplicateUnissuedData before [] :=
    ⟨unifiedInputs.publicProgram.image, unifiedInputs.publicProgram.initialClock, unifiedInputs.publicProgram.initialAligned⟩
  have unique := UnifiedReduced.Caller.worker_invocation_uniqueness_soundness (by decide +kernel) (by decide +kernel)
    accepted inputs unifiedInputs.initialization unifiedInputs.distinct
  exact (by decide +kernel : ¬ (duplicateUnissuedData.workers.rows.filter fun worker =>
    decide ((Delegation.Requests.fulfillment worker).time = (0, 0))).length ≤ 1) unique.unissued

theorem unified_all_worker_execution :
    UnifiedReduced.Caller.MixedWorkerExecution unifiedData before cells :=
  UnifiedReduced.Caller.all_worker_execution_soundness unifiedAccepted unifiedInputs

theorem prepared_all_worker_execution :
    UnifiedReduced.Caller.MixedWorkerExecution preparationData preparationBefore preparationCells :=
  UnifiedReduced.Caller.all_worker_execution_soundness preparationAccepted preparationInputs

/-- The clock-three group is exactly the unissued G worker, even with the later
    ordinary reset present. No issued-worker or positive invocation premise is used. -/
theorem prepared_unissued_clock_group {events : List MemoryAccess}
    (permutation : events.Perm (preparationData.mixedSteps.map transferEvent)) :
    (events.filter fun event => decide (event.1 = 3)).Perm (native.memorySteps.map transferEvent) := by
  have grouped := UnifiedReduced.Caller.Proofs.all_worker_clock_group (by decide +kernel) (by decide +kernel)
    preparationAccepted preparationInputs.publicProgram preparationInputs.initialization preparationInputs.distinct
    permutation (worker := native) (List.mem_singleton_self _)
  have clock : UnifiedReduced.Caller.Proofs.workerClock native = 3 := by decide +kernel
  simpa only [clock] using grouped

/-- One actual history now exposes the complete unissued call's states, x12
    zero to one, followed by the actual ordinary reset back to zero. -/
theorem prepared_unissued_prefix_states :
    ∃ (events current newer : List MemoryAccess) (finish after : Reference.RiscV.Sail.State),
      events.Perm (preparationData.mixedSteps.map transferEvent) ∧
      Trace.SailHistory preparationCells events preparationBefore after ∧
      events = newer ++ current ∧ current.Perm (native.memorySteps.map transferEvent) ∧
      Trace.SailHistory preparationCells current preparationBefore finish ∧
      Trace.SailHistory preparationCells newer finish after ∧
      (Cell.register 12).read preparationBefore = .ok 0 preparationBefore ∧
      (Cell.register 12).read finish = .ok 1 finish ∧
      (Cell.register 12).read after = .ok 0 after := by
  obtain ⟨events, after, permutation, _, history, _, unissued, _, terminal⟩ := prepared_all_worker_execution
  obtain ⟨current, newer, finish, split, grouped, call, rest, ports⟩ :=
    unissued native (List.mem_singleton_self _) (by decide +kernel)
  let port := native.ports[8]
  have nativePort : port ∈ native.ports := by
    simp [port, native, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts]
  obtain ⟨cell, _, address, read, written⟩ := ports port nativePort
  have code : port.address.code native.assignment = (Cell.register 12).addressCode := by decide +kernel
  have same := Trace.Proofs.cell_address_injective (address.trans code)
  subst cell
  have readValue : (readToken native.assignment port).word.toBitVec = (0 : BitVec 32) := by decide +kernel
  have writtenValue : (native.writeToken port).word.toBitVec = (1 : BitVec 32) := by decide +kernel
  let sink : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (6, 0), 0⟩
  have member : sink ∈ preparationData.machine.terminalMemory := by decide +kernel
  obtain ⟨last, _, code, actual⟩ := terminal sink member
  have same : last = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst last
  have finalValue : sink.word.toBitVec = (0 : BitVec 32) := by decide +kernel
  exact ⟨events, current, newer, finish, after, permutation, history, split, grouped, call, rest,
    readValue ▸ read, writtenValue ▸ written, finalValue ▸ actual⟩

/-- An empty machine path may have a zero public endpoint while the accepted
    unissued worker still runs. This is not a native boot configuration. -/
private def zeroInitialData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { unifiedData with machine := { unifiedData.machine with
      initial := { unifiedData.machine.initial with timestamp := (0, 0) }
      terminal := { unifiedData.machine.terminal with timestamp := (0, 0) } } }

private theorem zeroInitialAccepted : UnifiedReduced.Caller.MixedMemoryAccepted zeroInitialData [] := by
  refine ⟨?_, ?_, unifiedAccepted.memory⟩
  constructor
  · intro _ member; cases member
  · intro _ member; cases member
  · exact List.Perm.refl _
  · intro _ member; cases member
  · exact unifiedAccepted.workerConstraints
  · exact unifiedAccepted.workerActive
  · exact no_caller_virtual_matching
  · intro _ member; cases member

private theorem zeroInitialInputs : UnifiedReduced.Caller.MixedMemoryInputs zeroInitialData [] before [] [] cells := by
  refine ⟨⟨rfl, by change 0 < timestampBase ∧ 0 < timestampBase; norm_num [timestampBase],
    by decide +kernel⟩, unifiedInputs.ordinaryProgram,
    unifiedInputs.initialization, unifiedInputs.distinct, unifiedInputs.aligned,
    unifiedInputs.setup, unifiedInputs.tables, unifiedInputs.rounds⟩

private theorem zeroInitialCode : UnifiedReduced.Caller.CodeProfile zeroInitialData [] cells :=
  ⟨unifiedCode.ram, unifiedCode.ordinary, unifiedCode.callers⟩

theorem zero_initial_clock_unissued_accepted :
    UnifiedReduced.Caller.MixedMemoryAccepted zeroInitialData [] ∧
    (timeOfPair zeroInitialData.machine.initial.timestamp).value = 0 :=
  ⟨zeroInitialAccepted, by decide +kernel⟩

theorem zero_initial_clock_caller_cycles :
    UnifiedReduced.Caller.CallerCycleEffects zeroInitialData [] before cells :=
  UnifiedReduced.Caller.native_caller_cycles_soundness zeroInitialAccepted zeroInitialInputs zeroInitialCode

/-- Removing the supplied positive-clock premise keeps the actual state-changing
    unissued prefix, even with a zero public machine endpoint. -/
theorem zero_initial_clock_unissued_prefix :
    ∃ (events current newer : List MemoryAccess) (finish after : Reference.RiscV.Sail.State),
      events.Perm (zeroInitialData.mixedSteps.map transferEvent) ∧
      Trace.SailHistory cells events before after ∧
      events = newer ++ current ∧ current.Perm (native.memorySteps.map transferEvent) ∧
      Trace.SailHistory cells current before finish ∧ Trace.SailHistory cells newer finish after ∧
      (Cell.register 12).read before = .ok 0 before ∧ (Cell.register 12).read finish = .ok 1 finish := by
  obtain ⟨events, after, permutation, _, history, _, unissued, _, _⟩ :=
    UnifiedReduced.Caller.all_worker_execution_soundness zeroInitialAccepted zeroInitialInputs
  obtain ⟨current, newer, finish, split, grouped, call, rest, ports⟩ :=
    unissued native (List.mem_singleton_self _) (by decide +kernel)
  let port := native.ports[8]
  have nativePort : port ∈ native.ports := by
    simp [port, native, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts]
  obtain ⟨cell, _, address, read, written⟩ := ports port nativePort
  have code : port.address.code native.assignment = (Cell.register 12).addressCode := by decide +kernel
  have same := Trace.Proofs.cell_address_injective (address.trans code)
  subst cell
  have readValue : (readToken native.assignment port).word.toBitVec = (0 : BitVec 32) := by decide +kernel
  have writtenValue : (native.writeToken port).word.toBitVec = (1 : BitVec 32) := by decide +kernel
  exact ⟨events, current, newer, finish, after, permutation, history, split, grouped, call, rest,
    readValue ▸ read, writtenValue ▸ written⟩

/-- The actual ADDI cycle and earlier unissued worker share one history without
    supplying a positive initial-clock premise to cycle grouping. -/
theorem prepared_native_cycle_states :
    ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
      events.Perm (preparationData.mixedSteps.map transferEvent) ∧
      Trace.SailHistory preparationCells events preparationBefore after ∧
      UnifiedReduced.Caller.UnissuedPrefixExecution preparationCells events preparationBefore after native ∧
      UnifiedReduced.Caller.CycleExecution preparationData preparationCells events preparationBefore after preparationRow := by
  obtain ⟨events, after, permutation, _, history, _, unissued, cycles, _⟩ := prepared_all_worker_execution
  exact ⟨events, after, permutation, history, unissued native (List.mem_singleton_self _) (by decide +kernel),
    cycles preparationRow (List.mem_singleton_self _)⟩

theorem computed_hash_source_retains_unissued_worker :
    UnifiedReduced.Caller.HashControlPreparation preparationData [preparationEntry] 8 (.blakeG false) := by
  apply UnifiedReduced.Caller.HashControlPreparation.literal
  refine ⟨.uniform ?_, ?_, by decide +kernel, by decide +kernel⟩
  · intro entry member
    have same : entry = preparationEntry := List.mem_singleton.mp member
    subst entry
    rfl
  · have time : native.writeTime = 2 := by decide +kernel
    change ([native].filter fun worker => decide (4 < worker.writeTime ∧ worker.writeTime ≤ 8)) = []
    simp [time]

theorem computed_hash_preparation_retains_unissued_effect :
    preparationData.workers.prefixRows 8 = [native] ∧
      UnifiedReduced.Caller.PreparedBoundaryExecution preparationData preparationBefore preparationCells 8 12
        (UnifiedReduced.Caller.hashPreparation (.blakeG false)) := by
  refine ⟨control_preparation_after_unissued_worker.1, ?_⟩
  exact UnifiedReduced.Caller.hash_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) preparationAccepted preparationInputs computed_hash_source_retains_unissued_worker (by decide)

/-- Deriving a public selected region leaves the state-changing unissued worker
    in the prefix; the selected region itself has no workers. -/
theorem computed_public_region_retains_unissued_worker :
    preparationData.workers.prefixRows 8 = [native] ∧
      UnifiedReduced.Caller.ProgramCallerWindow preparationData .blakeG 8 8 ∧
      (preparationData.workers.windowRows 8 8).length = 0 := by
  have registry : UnifiedReduced.Caller.WrappedSequentialProgram [preparationEntry] := by
    constructor
    · intro entry member
      have same := List.mem_singleton.mp member
      subst entry
      exact .sequential (.arithmetic (.addi _ _ _))
    · intro entry member
      have same := List.mem_singleton.mp member
      subst entry
      decide +kernel
  have region : UnifiedReduced.Caller.WrappedProgramCallerRegion preparationData [preparationEntry] .blakeG 8 8 := by
    constructor
    · intro _ _ _ lower upper; omega
    · intro _ _ _ lower upper; omega
  have schedule := UnifiedReduced.Caller.hash_prepared_public_window_schedule_soundness
    (by decide +kernel) (by decide +kernel) preparationInputs.setup preparationAccepted
    preparationInputs.publicProgram preparationInputs.ordinaryProgram registry
    computed_hash_source_retains_unissued_worker region (by decide) (by decide) (by decide) (by decide +kernel)
  refine ⟨control_preparation_after_unissued_worker.1, schedule, ?_⟩
  rw [← schedule.workerCount]
  simpa using schedule.machineCount

theorem computed_protocol_retains_unissued_g :
    UnifiedReduced.Caller.ComputedPreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] ∧
    native ∈ preparationData.workers.rows ∧
    ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) ∧
    UnifiedReduced.Caller.MixedMemoryInputs preparationData [preparationEntry] preparationBefore [] [0] preparationCells := by
  have context := UnifiedReduced.Caller.Proofs.literal_computed_protocol_inputs prepared_protocol_inputs_keep_unissued
  exact ⟨context, List.mem_singleton_self _, by decide +kernel,
    UnifiedReduced.Caller.computed_protocol_memory_soundness (by decide +kernel) (by decide +kernel)
      preparationAccepted context⟩

theorem computed_public_protocol_retains_unissued_g :
    UnifiedReduced.Caller.WrappedProgramComputedPreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] ∧
    UnifiedReduced.Caller.RoundWorkerCoverage preparationData [] ∧
    native ∈ preparationData.workers.rows ∧
    ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) := by
  have old := wrapped_program_inputs_keep_unissued
  have context : UnifiedReduced.Caller.WrappedProgramComputedPreparedProtocolInputs preparationData preparationBefore
      [] [0] preparationCells [preparationEntry] [] := by
    refine ⟨old.toProtocolContextInputs, old.registry, ?_, old.coverage⟩
    intro _ member; cases member
  have code : UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage preparationData [] := by
    intro _ member; cases member
  have covered := (UnifiedReduced.Caller.wrapped_program_computed_round_coverage_soundness
    (by decide +kernel) (by decide +kernel) preparationAccepted context.toProtocolContextInputs context.registry
    context.scopes code).1
  exact ⟨context, covered, List.mem_singleton_self _, by decide +kernel⟩

private def operandAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 5 then 12
  else if column = 34 then 2
  else if column = 36 ∨ column = 50 then 1
  else if column = 46 then 4
  else if column = 40 then 0
  else preparationAssignment column
private def operandRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, operandAssignment⟩
private def operandBefore : Reference.RiscV.Sail.State := Reference.RiscV.Sail.wordWriteState before 0 0x00060613
private def operandEntry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0x00060613, .ITYPE (0, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, ⟨0, 0⟩, 1, 0⟩⟩
private def operandData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { preparationData with machine := { preparationData.machine with
      rows := [operandRow]
      rom := UnifiedReduced.Setup.table operandBefore
      initial := operandRow.start
      terminal := operandRow.finish
      terminalMemory := ⟨(Cell.register 0).addressCode, (5, 0), 0⟩ ::
        ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair 1 0⟩ ::
        data.terminal.filter (fun token => token.address != (Cell.register 12).addressCode) } }

private theorem operandCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment operandAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table operandBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, operandAssignment, preparationAssignment, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (with_unfolding_all refine ⟨⟨0, by decide⟩, ?_⟩
       dsimp only
       rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
       simp only [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
         UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
       with_unfolding_all decide +kernel)
    | decide +kernel

private theorem operandClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment operandAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem operandAccepted :
    UnifiedReduced.Caller.MixedMemoryAccepted operandData [operandEntry] := by
  constructor
  · constructor
    · intro current member
      have same : current = operandRow := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append operandCore operandClocks
    · intro current member
      have same : current = operandRow := List.mem_singleton.mp member
      subst current
      rfl
    · exact List.Perm.swap _ _ []
    · intro current member
      have empty : operandData.callers = [] := by decide +kernel
      rw [empty] at member
      cases member
    · exact sharedAccepted.workerConstraints
    · exact sharedAccepted.workerActive
    · exact no_caller_virtual_matching
  · intro current member _
    have same : current = operandRow := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, operandRow.decoderQuery = ([operandEntry].get i).query
    exact ⟨0, by decide +kernel⟩
  · decide +kernel

private theorem operandProgram :
    UnifiedReduced.Mixed.programImage operandBefore [0] = some [operandEntry] := by
  have bytes : (Cell.ram 0).read operandBefore = .ok 0x00060613 operandBefore :=
    Reference.RiscV.Sail.written_word_read before 0 _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x00060613) operandBefore =
      .ok operandEntry.instruction operandBefore := by with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields operandEntry.instruction = some operandEntry.data := by
    with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem operandImage :
    initialImage operandBefore preparationCells = some operandData.machine.initialMemory := by
  have x10 : Cell.read (.register 10) operandBefore = .ok 4194304 operandBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [operandBefore, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) operandBefore = .ok 4194368 operandBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [operandBefore, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  have x12 : Cell.read (.register 12) operandBefore = .ok 0 operandBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [operandBefore, Reference.RiscV.Sail.wordWriteState, before]
  have zero : Cell.read (.register 0) operandBefore = .ok 0 operandBefore := rfl
  simp only [initialImage, preparationCells, cells, List.mapM_cons, List.mapM_nil, zero, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, operandBefore, Reference.RiscV.Sail.wordWriteState,
    before, Std.ExtHashMap.getElem_insert, Cell.initialToken, operandData, data, native,
    Delegation.Row.memorySteps, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, row, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
  all_goals decide +kernel

private theorem operandInputs :
    UnifiedReduced.Caller.MixedMemoryInputs operandData [operandEntry] operandBefore [] [0] preparationCells := by
  refine ⟨⟨rfl, ?_, by decide⟩, operandProgram, operandImage, by decide, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · intro cell member
    simp [preparationCells, cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  · intro current member family
    have same : current = native := List.mem_singleton.mp member
    subst current
    cases family

private theorem operandScope : UnifiedReduced.Caller.RegisterImmediatePreparation operandData [operandEntry] 8 12 12 0 := by
  refine ⟨⟨?_, ?_⟩, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    exact .sequential (.arithmetic (.addi _ _ _))
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    decide +kernel
  · intro entry member _
    have same := List.mem_singleton.mp member
    subst entry
    rfl

theorem register_preparation_retains_unissued_effect :
    UnifiedReduced.Caller.RegisterImmediatePreparedBoundaryExecution operandData operandBefore preparationCells 8 12 12 0 :=
  UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) operandAccepted operandInputs operandScope (by decide) (by decide)

theorem register_preparation_uses_actual_unissued_operand :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess)
      (atSource atCut : Reference.RiscV.Sail.State),
      events.Perm ((operandData.prefixSteps 4).map transferEvent) ∧
      Trace.SailHistory preparationCells events operandBefore atSource ∧
      Trace.SailHistory preparationCells (Trace.rowEvents 1 operandRow).reverse atSource atCut ∧
      (operandData.machine.initialMemory ++ (operandData.prefixSteps 8).map Prod.snd).Perm
        (tokens ++ (operandData.prefixSteps 8).map Prod.fst) ∧
      (Cell.register 12).read operandBefore = .ok 0 operandBefore ∧
      (Cell.register 12).read atSource = .ok 1 atSource ∧
      (Cell.register 12).read atCut = .ok 1 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 6 ∧ token.word = Arithmetic.Word.ofBitVec 1 := by
  obtain ⟨row, member, _, tokens, events, atSource, atCut, permutation, past, native, matching, value, read, written, token, present, address, time, word⟩ :=
    register_preparation_retains_unissued_effect
  have same := List.mem_singleton.mp member
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := operandAssignment)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode operandAssignment) = 1 := by decide +kernel
  rw [operand] at actual
  have equal : value = 1 := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have initial : (Cell.register 12).read operandBefore = .ok 0 operandBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [operandBefore, Reference.RiscV.Sail.wordWriteState, before]
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, matching, initial, actual, written,
    token, present, address, time, word⟩

private def dataflowAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 0 then 4
  else if column = 2 || column = 30 || column = 46 then 8
  else if column = 32 then 12
  else if column = 5 then 12
  else if column = 34 then 6
  else if column = 40 then 5
  else if column = 48 then 0
  else if column = 8 || column = 50 then 128
  else preparationAssignment column
private def dataflowRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, dataflowAssignment⟩
private def dataflowBefore : Reference.RiscV.Sail.State :=
  Reference.RiscV.Sail.wordWriteState preparationBefore 4 0x08060613
private def dataflowEntry : UnifiedReduced.ProgramEntry :=
  ⟨4, 0x08060613, .ITYPE (128, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, ⟨128, 0⟩, 1, 0⟩⟩
private def dataflowData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { preparationData with machine := { preparationData.machine with
      rows := [dataflowRow, preparationRow]
      rom := UnifiedReduced.Setup.table dataflowBefore
      terminal := dataflowRow.finish
      terminalMemory := ⟨(Cell.register 0).addressCode, (9, 0), 0⟩ ::
        ⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 128 0⟩ ::
        data.terminal.filter (fun token => token.address != (Cell.register 12).addressCode) } }

private theorem dataflowCore (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (if second then dataflowAssignment else preparationAssignment))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table dataflowBefore)) := by
  cases second
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, dataflowAssignment, preparationAssignment, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (with_unfolding_all refine ⟨⟨0, by decide⟩, ?_⟩
       dsimp only
       rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
       simp only [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
         UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
       with_unfolding_all decide +kernel)
    | decide +kernel

private theorem dataflowClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment dataflowAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem dataflowAccepted :
    UnifiedReduced.Caller.MixedMemoryAccepted dataflowData [preparationEntry, dataflowEntry] := by
  constructor
  · constructor
    · intro current member
      have rows : current = dataflowRow ∨ current = preparationRow := by simpa [dataflowData] using member
      rcases rows with rfl | rfl
      · exact Verification.holds_append (dataflowCore true) dataflowClocks
      · exact Verification.holds_append (dataflowCore false) preparationClocks
    · intro current member
      have rows : current = dataflowRow ∨ current = preparationRow := by simpa [dataflowData] using member
      rcases rows with rfl | rfl <;> decide +kernel
    · change [preparationRow.start, dataflowRow.finish, preparationRow.finish].Perm
        [dataflowRow.finish, dataflowRow.start, preparationRow.start]
      have same : preparationRow.finish = dataflowRow.start := rfl
      rw [same]
      exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
    · intro current member
      have empty : dataflowData.callers = [] := by decide +kernel
      rw [empty] at member
      cases member
    · exact sharedAccepted.workerConstraints
    · exact sharedAccepted.workerActive
    · have empty : dataflowData.calls = [] := by decide +kernel
      rw [empty]
      exact no_caller_virtual_matching
  · intro current member _
    have rows : current = dataflowRow ∨ current = preparationRow := by simpa [dataflowData] using member
    rcases rows with rfl | rfl
    · change ∃ i : Fin 2, dataflowRow.decoderQuery = ([preparationEntry, dataflowEntry].get i).query
      exact ⟨1, by decide +kernel⟩
    · change ∃ i : Fin 2, preparationRow.decoderQuery = ([preparationEntry, dataflowEntry].get i).query
      exact ⟨0, by decide +kernel⟩
  · decide +kernel

private theorem dataflowProgram :
    UnifiedReduced.Mixed.programImage dataflowBefore [0, 4] = some [preparationEntry, dataflowEntry] := by
  have first : (Cell.ram 0).read dataflowBefore = .ok 0x00000613 dataflowBefore :=
    Reference.RiscV.Sail.written_word_disjoint 4 0x08060613 (by decide)
      (Reference.RiscV.Sail.written_word_read before 0 _)
  have second : (Cell.ram 4).read dataflowBefore = .ok 0x08060613 dataflowBefore :=
    Reference.RiscV.Sail.written_word_read preparationBefore 4 _
  have decodeFirst : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x00000613) dataflowBefore =
      .ok preparationEntry.instruction dataflowBefore := by with_unfolding_all rfl
  have decodeSecond : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x08060613) dataflowBefore =
      .ok dataflowEntry.instruction dataflowBefore := by with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields preparationEntry.instruction = some preparationEntry.data := by
    with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields dataflowEntry.instruction = some dataflowEntry.data := by
    with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, decodeFirst, decodeSecond, fieldsFirst, fieldsSecond, bind, Option.bind, pure]
  rfl

private theorem dataflowImage :
    initialImage dataflowBefore preparationCells = some dataflowData.machine.initialMemory := by
  have x10 : Cell.read (.register 10) dataflowBefore = .ok 4194304 dataflowBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [dataflowBefore, preparationBefore, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) dataflowBefore = .ok 4194368 dataflowBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [dataflowBefore, preparationBefore, Reference.RiscV.Sail.wordWriteState, before, Std.ExtDHashMap.get?_insert]
  have x12 : Cell.read (.register 12) dataflowBefore = .ok 0 dataflowBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [dataflowBefore, preparationBefore, Reference.RiscV.Sail.wordWriteState, before]
  have zero : Cell.read (.register 0) dataflowBefore = .ok 0 dataflowBefore := rfl
  simp only [initialImage, preparationCells, cells, List.mapM_cons, List.mapM_nil, zero, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, dataflowBefore, Reference.RiscV.Sail.wordWriteState,
    preparationBefore, before, Std.ExtHashMap.getElem_insert, Cell.initialToken, dataflowData, data, native,
    Delegation.Row.memorySteps, Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, row, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
  all_goals decide +kernel

private theorem dataflowInputs :
    UnifiedReduced.Caller.MixedMemoryInputs dataflowData [preparationEntry, dataflowEntry] dataflowBefore [] [0, 4] preparationCells := by
  refine ⟨⟨rfl, ?_, by decide⟩, dataflowProgram, dataflowImage, by decide, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · intro cell member
    simp [preparationCells, cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  · intro current member family
    have same : current = native := List.mem_singleton.mp member
    subst current
    cases family

private theorem dataflowRegistry : UnifiedReduced.Caller.WrappedSequentialProgram [preparationEntry, dataflowEntry] := by
  constructor
  · intro current member
    have entries : current = preparationEntry ∨ current = dataflowEntry := by simpa using member
    rcases entries with rfl | rfl
    all_goals exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = preparationEntry ∨ current = dataflowEntry := by simpa using member
    rcases entries with rfl | rfl <;> decide

private theorem dataflowScope : UnifiedReduced.Caller.LiteralAddiPreparation
    dataflowData [preparationEntry, dataflowEntry] 12 12 12 (.addi 0) 128 := by
  refine ⟨⟨.wrappedSequential (by decide) dataflowBefore rfl dataflowRegistry ?_, by decide +kernel,
    by decide +kernel, by decide +kernel⟩,
    ⟨dataflowRegistry, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    by decide, ?_⟩
  · intro current member address
    have entries : current = preparationEntry ∨ current = dataflowEntry := by simpa using member
    rcases entries with rfl | rfl
    · rfl
    · change (4 : BitVec 32) = 0 at address
      contradiction
  · intro current member address
    have entries : current = preparationEntry ∨ current = dataflowEntry := by simpa using member
    rcases entries with rfl | rfl
    · change (0 : BitVec 32) = 4 at address
      contradiction
    · rfl
  · rw [Trace.Proofs.image_addresses dataflowInputs.initialization]
    exact dataflowInputs.distinct

theorem literal_addi_protocol_retains_unissued_g :
    UnifiedReduced.Caller.PreparedBoundaryExecution dataflowData dataflowBefore preparationCells 12 12
      (UnifiedReduced.Caller.hashPreparation (.blakeG true)) ∧
    native ∈ dataflowData.workers.rows ∧
    ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) := by
  refine ⟨?_, List.mem_singleton_self _, by decide +kernel⟩
  exact UnifiedReduced.Caller.literal_addi_hash_preparation_soundness (span := .blakeG true) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) dataflowAccepted dataflowInputs dataflowScope.seed dataflowScope.step
    (by decide) (by decide +kernel) (by decide)

theorem literal_addi_retains_actual_unissued_prefix :
    ∃ sequence : UnifiedReduced.Caller.WindowSequence babyBearModulus,
      sequence.Realizes dataflowData dataflowBefore preparationCells 4 [(4, 8), (8, 12)] ∧
      (Cell.register 12).read sequence.atInitial = .ok 1 sequence.atInitial := by
  obtain ⟨sequence, history⟩ := UnifiedReduced.Caller.mixed_window_sequence_soundness
    (cut := 4) (windows := [(4, 8), (8, 12)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) dataflowAccepted dataflowInputs
    (by decide) (by decide) (by simp [UnifiedReduced.Caller.WindowsOrdered])
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (2, 0), Nat.pair 1 0⟩
  have produced : token ∈ dataflowData.machine.initialMemory ++ (dataflowData.prefixSteps 4).map Prod.snd := by decide +kernel
  have notRead : token ∉ (dataflowData.prefixSteps 4).map Prod.fst := by decide +kernel
  have present : token ∈ sequence.initial := by
    rcases List.mem_append.mp (history.prefixMatching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  obtain ⟨cell, _, address, actualRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read history.boundary present
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have bits : token.word.toBitVec = (1 : BitVec 32) := by
    simp only [token, MemoryToken.word, Nat.unpair_pair]
    rfl
  rw [bits] at actualRead
  exact ⟨sequence, history, actualRead⟩

theorem register_chain_protocol_retains_unissued_g :
    UnifiedReduced.Caller.PreparedBoundaryExecution dataflowData dataflowBefore preparationCells 12 12
      (UnifiedReduced.Caller.hashPreparation (.blakeG true)) ∧
    native ∈ dataflowData.workers.rows ∧ ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) := by
  refine ⟨?_, List.mem_singleton_self _, by decide +kernel⟩
  have preparation := UnifiedReduced.Caller.PublicRegisterPreparation.addi
    (.literal dataflowScope.seed) dataflowScope.step (by decide : (12 : BitVec 5) ≠ 0)
  exact UnifiedReduced.Caller.register_chain_hash_preparation_soundness (span := .blakeG true)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) dataflowAccepted dataflowInputs preparation
    (by decide +kernel) (by decide)

theorem register_chain_retains_actual_unissued_prefix :
    ∃ sequence : UnifiedReduced.Caller.WindowSequence babyBearModulus,
      sequence.Realizes dataflowData dataflowBefore preparationCells 4 [(4, 8), (8, 12)] ∧
      (Cell.register 12).read sequence.atInitial = .ok 1 sequence.atInitial :=
  literal_addi_retains_actual_unissued_prefix

theorem register_dataflow_protocol_retains_unissued_g :
    UnifiedReduced.Caller.PreparedBoundaryExecution dataflowData dataflowBefore preparationCells 12 12
      (UnifiedReduced.Caller.hashPreparation (.blakeG true)) ∧
    native ∈ dataflowData.workers.rows ∧ ¬ Delegation.Requests.Live (Delegation.Requests.fulfillment native) := by
  refine ⟨?_, List.mem_singleton_self _, by decide +kernel⟩
  have prior := UnifiedReduced.Caller.PublicRegisterDataflow.prepared
    (UnifiedReduced.Caller.PublicRegisterPreparation.literal dataflowScope.seed)
  exact UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) dataflowAccepted dataflowInputs prior dataflowScope.step
    (by decide) (by decide +kernel) (by decide)

theorem register_dataflow_retains_actual_unissued_prefix :
    ∃ sequence : UnifiedReduced.Caller.WindowSequence babyBearModulus,
      sequence.Realizes dataflowData dataflowBefore preparationCells 4 [(4, 8), (8, 12)] ∧
      (Cell.register 12).read sequence.atInitial = .ok 1 sequence.atInitial :=
  literal_addi_retains_actual_unissued_prefix

open Arithmetic Reference.RiscV.Sail Reference.Sail

private theorem segmentationContext : UnifiedReduced.Caller.ProtocolContextInputs unifiedData before [] [] cells [] :=
  ⟨unifiedInputs.publicProgram, unifiedInputs.ordinaryProgram, unifiedInputs.initialization,
    unifiedInputs.distinct, unifiedInputs.aligned, unifiedInputs.setup, unifiedInputs.tables⟩
private theorem segmentationRegistry : UnifiedReduced.Caller.WrappedSequentialProgram [] := by
  constructor <;> intro _ member <;> cases member

theorem unified_unissued_hash_partition : UnifiedReduced.Caller.IssuedHashSegmentation unifiedData [] := by
  apply UnifiedReduced.Caller.hash_segmentation_soundness (cut := 4) (by decide +kernel) (by decide +kernel)
    unifiedAccepted segmentationContext segmentationRegistry
  · intro _ member; cases member
  · trivial
  · intro _ member; cases member

theorem unified_hash_partition_retains_unissued_effect :
    unifiedData.workers.rows = [native] ∧ UnifiedReduced.Caller.issuedHashWorkers unifiedData = [] ∧
    ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
      events.Perm (unifiedData.mixedSteps.map transferEvent) ∧
      SailHistory cells events before after ∧
      (Cell.register 12).read before = .ok 0 before ∧ (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨events, after, _, permutation, history, initial, terminal⟩ := unified_unissued_control_update
  exact ⟨rfl, by decide +kernel, events, after, permutation, history, initial, terminal⟩

theorem unified_hash_partition_is_not_all_workers :
    ¬ ([] : List (Delegation.Row babyBearModulus)).Perm unifiedData.workers.rows := by
  intro permutation
  have length := permutation.length_eq
  change 0 = 1 at length
  contradiction

private def issuedAssignment (column : Nat) : ZMod babyBearModulus := if column = 1 then 5 else row column
private def issuedWorker : Delegation.Row babyBearModulus := ⟨.blakeG, issuedAssignment⟩
private def issuedCallerAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 || column = 30 || column = 46 then 4
  else if column = 32 then 8
  else if column = 4 || column = 18 || column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
  else if column = 6 || column = 38 then Delegation.Requests.csr .blakeG else 0
private def issuedCaller : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, issuedCallerAssignment⟩
private def issuedBefore : Reference.RiscV.Sail.State :=
  wordWriteState before 0 (Tests.DelegationCaller.entry .blakeG).bits
private def issuedCells : List Cell := .register 0 :: cells
private def issuedData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [issuedCaller]
    rom := UnifiedReduced.Setup.table issuedBefore
    initial := issuedCaller.start
    terminal := issuedCaller.finish
    initialMemory := (Cell.register 0).initialToken 0 :: issuedWorker.memorySteps.map Prod.fst
    terminalMemory := UnifiedReduced.Caller.destinationToken issuedCallerAssignment :: issuedWorker.memorySteps.map Prod.snd }
  workers := { sharedWorkers with rows := [issuedWorker], initial := [], terminal := [] }
  program := [Tests.DelegationCaller.entry .blakeG]
private theorem issuedCore : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedAssignment)
    (Blake2G.importedConstraints table) := by
  simpa [Blake2G.importedConstraints, FlatOperation.ConstraintsHoldFlat, Verification.environment,
    Expression.eval, Lookup.Contains, Table.toRaw, fromElements, Verification.range16, issuedAssignment, row] using core
private theorem issuedClocks : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedAssignment)
    Blake2G.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 20 := by simpa only [Blake2G.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel
private theorem issuedCallerCore : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedCallerAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table issuedBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, issuedCallerAssignment, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (with_unfolding_all refine ⟨⟨0, by decide⟩, ?_⟩
       dsimp only
       rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
       simp only [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
         UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
       with_unfolding_all decide +kernel)
    | decide +kernel

private theorem issuedCallerClocks : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedCallerAssignment)
    UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel
private theorem issuedAccepted : UnifiedReduced.Caller.MixedMemoryAccepted issuedData [] := by
  constructor
  · constructor
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      exact Verification.holds_append issuedCallerCore issuedCallerClocks
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      rfl
    · exact List.Perm.swap _ _ []
    · intro actual member
      have same : actual = issuedCaller := List.mem_singleton.mp member
      subst actual
      exact ⟨(0 : Fin 1), by decide +kernel⟩
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      exact Verification.holds_append issuedCore issuedClocks
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      rfl
    · have same : issuedData.calls = issuedData.fulfillments := by decide +kernel
      rw [← same]
      exact List.perm_append_comm
  · intro actual member ordinary
    have same := List.mem_singleton.mp member
    subst actual
    exact False.elim (ordinary (List.mem_singleton_self _))
  · decide +kernel
private theorem issuedInitialization : initialImage issuedBefore issuedCells = some issuedData.machine.initialMemory := by
  have seeds : initialImage before issuedCells = some issuedData.machine.initialMemory := by
    have same : issuedWorker.memorySteps.map Prod.fst = native.memorySteps.map Prod.fst := by decide +kernel
    change initialImage before (.register 0 :: cells) = some ((Cell.register 0).initialToken 0 :: issuedWorker.memorySteps.map Prod.fst)
    rw [same]
    have x0 : (Cell.register 0).read before = .ok 0 before := rfl
    have initial := initialized
    dsimp only [initialImage] at initial
    simp only [initialImage, List.mapM_cons, x0]
    rw [initial]
    rfl
  apply Trace.Proofs.image_frame seeds
  intro cell member value read
  cases cell with
  | register index => exact rX_register_frame (by dsimp only [issuedBefore, wordWriteState]) index read
  | ram address =>
    have lower : 4 ≤ address.toNat := by
      simp [issuedCells, cells] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    exact written_word_disjoint 0 _ (Or.inr lower) read
private theorem issuedInputs : UnifiedReduced.Caller.MixedMemoryInputs issuedData [] issuedBefore [0] [] issuedCells := by
  refine ⟨?_, rfl, issuedInitialization, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · constructor
    · have bytes : (Cell.ram 0).read issuedBefore =
          .ok (Tests.DelegationCaller.entry .blakeG).bits issuedBefore := written_word_read _ 0 _
      have decoded : run
          (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .blakeG).bits) issuedBefore =
          .ok (Tests.DelegationCaller.entry .blakeG).instruction issuedBefore := Tests.DelegationCaller.original_decoder .blakeG issuedBefore
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .blakeG).instruction =
          some (Tests.DelegationCaller.entry .blakeG).data := Tests.DelegationCaller.metadata .blakeG
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · decide +kernel
  · intro cell member
    simp [issuedCells, cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  · intro actual member family
    have same := List.mem_singleton.mp member
    subst actual
    cases family
private def issuedWindow : UnifiedReduced.Caller.HashWindow := ⟨.blakeG true, 4, 8⟩
private theorem issuedCoverage : UnifiedReduced.Caller.ProgramHashCallerCoverage issuedData [issuedWindow] := by
  intro entry member _ clock lower upper aligned address
  have same := List.mem_singleton.mp member
  subst entry
  have selected : clock = 4 := by change 4 ≤ clock at lower; change clock + 4 ≤ 8 at upper; omega
  subst clock
  exact ⟨issuedWindow, List.mem_singleton_self _, by decide, by decide, rfl⟩

theorem issued_hash_worker_covered :
    ∃ window ∈ [issuedWindow], issuedWorker ∈ issuedData.workers.windowRows window.lower window.upper := by
  have covered := UnifiedReduced.Caller.Proofs.program_hash_worker_coverage (by decide +kernel) (by decide +kernel)
    issuedInputs.setup issuedAccepted issuedInputs.publicProgram issuedInputs.ordinaryProgram segmentationRegistry
    (windows := [issuedWindow]) (by intro window member; have same := List.mem_singleton.mp member; subst window; decide) issuedCoverage
  exact (covered issuedWorker (List.mem_singleton_self _) (by decide)).mpr (by decide +kernel)

theorem issued_hash_missing_window_rejected : ¬ UnifiedReduced.Caller.ProgramHashCallerCoverage issuedData [] := by
  intro coverage
  obtain ⟨window, member, _⟩ := coverage (Tests.DelegationCaller.entry .blakeG) (List.mem_singleton_self _)
    (by decide) 4 (by decide) (by decide) (by decide) rfl
  cases member

theorem issued_hash_partial_protocol_rejected :
    ¬ UnifiedReduced.Caller.WrappedProgramComputedProtocolWindowInputs issuedData [] issuedWindow := by
  intro scope
  have duration := scope.duration
  change 8 = 4 + 4 * 56 at duration
  contradiction

theorem issued_hash_worker_executes : UnifiedReduced.Caller.MixedMemoryEffects issuedData issuedBefore issuedCells :=
  UnifiedReduced.Caller.mixed_memory_soundness issuedAccepted issuedInputs

theorem unissued_hash_mixed_cycles [Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    UnifiedReduced.Caller.MixedCycleEffects unifiedData [] before cells := by
  have effects := UnifiedReduced.Caller.Proofs.mixed_memory_effects unifiedAccepted unifiedInputs
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  apply UnifiedReduced.Caller.Proofs.mixed_cycle_effects_at unifiedAccepted unifiedInputs
    effects permutation order history unifiedCode _ terminal
  intro row member
  cases member

theorem unissued_worker_padding_boundary :
    UnifiedReduced.Caller.Padding.AcceptedLayout unifiedData [] :=
  UnifiedReduced.Caller.Padding.Proofs.layout_of_accepted unifiedAccepted

theorem unissued_worker_survives_padding :
    native ∈ (UnifiedReduced.Caller.Padding.active unifiedData).workers.rows ∧
    (Delegation.Requests.fulfillment native).time = (0, 0) := by
  refine ⟨UnifiedReduced.Caller.Padding.Proofs.retained_worker (by exact List.mem_singleton_self _)
    (unifiedAccepted.workerActive native (List.mem_singleton_self _)), ?_⟩
  decide +kernel

end Tests.DelegationZeroInvocation
