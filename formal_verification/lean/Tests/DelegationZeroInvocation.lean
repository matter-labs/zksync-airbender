import Airbender.Review.Delegation.CallerTheorems
import Airbender.Review.UnifiedReduced.Theorems
import Airbender.Proofs.Blake2G.Claims
import Airbender.Proofs.Delegation.Requests
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

end Tests.DelegationZeroInvocation
