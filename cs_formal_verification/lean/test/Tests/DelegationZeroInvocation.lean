import Slop.Sail.ResetState
import Slop.Final.Circuits.AddSub.CallerTheorems
import Slop.Final.Trace.Delegation.CallerTheorems
import Slop.Final.Trace.UnifiedReduced.Theorems
import Slop.Blake2G.Claims
import Slop.Delegation.Requests
import Slop.Sail.WordMemoryState
import Mathlib.Tactic.IntervalCases

namespace Tests.DelegationZeroInvocation
open Airbender Trace
set_option warningAsError true
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
private noncomputable def before : Reference.RiscV.Sail.State where
  regs := Reference.RiscV.Sail.resetMachine.regs.insert .x10 (4194304 : BitVec 32)
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

private theorem airbender_before : Reference.RiscV.Sail.Configured before := by
  configured_fixture [before]

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
  · refine ⟨⟨rfl, ?_, rfl, airbender_before⟩, initialized, by decide, ?_⟩
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

private noncomputable def mixedData : Delegation.Caller.RequestTrace babyBearModulus :=
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
      sharedInputs.publicProgram.initialAligned, sharedInputs.publicProgram.configuration⟩,
    sharedInputs.initialization,
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

private noncomputable def unifiedData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
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
  refine ⟨⟨rfl, sharedInputs.publicProgram.initialClock, sharedInputs.publicProgram.initialAligned,
      sharedInputs.publicProgram.configuration⟩,
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
private noncomputable def preparationBefore : Reference.RiscV.Sail.State :=
  Reference.RiscV.Sail.wordWriteState before 0 0x00000613

private theorem airbender_preparationBefore : Reference.RiscV.Sail.Configured preparationBefore := by
  configured_fixture [preparationBefore, Reference.RiscV.Sail.wordWriteState, before]
private def preparationCells : List Cell := .register 0 :: cells
private def preparationEntry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0x00000613, (UnifiedReduced.Caller.ControlLiteral.addi 0).instruction 12,
    ⟨.machine, 0, 0, 12, ⟨0, 0⟩, 1, 0⟩⟩
private noncomputable def preparationData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
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
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

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
  have decoded : Airbender.Reference.RiscV.Sail.decodeOnReset 0x00000613 = some preparationEntry.instruction :=
    by decode_on_reset
  have fields : UnifiedReduced.Mixed.decoderFields preparationEntry.instruction = some preparationEntry.data := by
    with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageWith, List.mapM_cons, List.mapM_nil,
    programEntryWith, bytes, decoded, fields, bind, Option.bind, pure]
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
  refine ⟨⟨rfl, ?_, by decide, airbender_preparationBefore⟩, preparationProgram, preparationImage, by decide, ?_, rfl, rfl, ?_⟩
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
private noncomputable def fabricatedPreparationData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
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

private theorem prepared_protocol_inputs_keep_unissued :
    UnifiedReduced.Caller.PreparedProtocolInputs preparationData preparationBefore [] [0]
      preparationCells [preparationEntry] [] := by
  have context := preparationInputs
  refine ⟨context.publicProgram, context.ordinaryProgram, context.initialization, context.distinct,
    context.aligned, context.setup, context.tables, ?_, ?_⟩
  · intro region member
    cases member
  · intro row member same
    have only : row = native := List.mem_singleton.mp member
    subst row
    cases same

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

end Tests.DelegationZeroInvocation
