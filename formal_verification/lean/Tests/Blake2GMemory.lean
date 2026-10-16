import Airbender.Proofs.Blake2G.Claims
import Airbender.Review.Trace.Workers.Blake2G.ReferenceCalls
import Mathlib.Tactic.IntervalCases

set_option Elab.async false

namespace Tests.Blake2GMemory
open Airbender Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def row (column : Nat) : ZMod babyBearModulus :=
  if column = 0 ∨ column = 5 ∨ column = 12 then 1
  else if column = 1 ∨ column = 8 then 4
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

theorem native_full_reference_call :
    ∃ events after, events.Perm (data.steps.map transferEvent) ∧
      SailHistory cells events before after ∧ Blake2G.Call.Executes before after := by
  obtain ⟨events, after, permutation, _, history, _⟩ := native_operation_execution.1
  have localPerm : events.Perm (native.memorySteps.map transferEvent) := by
    simpa [data, Delegation.MemoryData.steps] using permutation
  have aligned : ∀ cell ∈ cells, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  have observed := Delegation.Proofs.row_atomic_observations (by decide) accepted
    interface.publicState.toBoundaryInputs (row := native) (List.mem_singleton_self _) history localPerm aligned
    (Delegation.Proofs.boundary_readable interface.publicState.toBoundaryInputs)
  have abi : Blake2G.Call.ABI (Blake2G.Call.Proofs.nativeArguments 0 row).addresses := by
    refine ⟨rfl, by decide +kernel, ?_, ?_, ?_, ?_⟩
    all_goals try unfold Arithmetic.Word.Bounded
    all_goals decide +kernel
  have reference := Blake2G.Call.Proofs.executes (p := babyBearModulus) (by decide) (by decide)
    (w := row) (register := 0) core abi (by decide) (by decide)
    (fun port member => by
      obtain ⟨i, bound, rfl⟩ := Array.mem_iff_getElem.mp member
      have short : i < 9 := by exact bound
      interval_cases i
      all_goals unfold Arithmetic.Word.Bounded
      all_goals decide +kernel +revert)
    history localPerm (fun port member => by
      obtain ⟨cell, _, code, read, _⟩ := observed port member
      exact ⟨cell, code, read⟩)
  exact ⟨events, after, permutation, history, reference⟩


private def boundaryRow (column : Nat) : ZMod babyBearModulus :=
  if 83 ≤ column ∧ column < 110 ∧ (column - 83) % 3 = 0 then 1 else row column

private theorem boundaryTableQuery (i : Fin 19) :
    ((FlatOperation.lookups (Blake2G.importedConstraints table)).get
      ⟨i.val + 2, by rw [Blake2G.lookup_count]; omega⟩).Contains
        (Verification.environment boundaryRow) := by
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

private theorem boundaryCore : FlatOperation.ConstraintsHoldFlat (Verification.environment boundaryRow)
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
    · have source := boundaryTableQuery ⟨i - 2, by omega⟩
      have position : i - 2 + 2 = i := by omega
      simpa only [List.get_eq_getElem, Fin.val_mk, position] using source

private theorem boundaryClocks : FlatOperation.ConstraintsHoldFlat (Verification.environment boundaryRow)
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
      Expression.eval, Verification.environment, boundaryRow, row, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

private def retimeSeed (token : MemoryToken babyBearModulus) : MemoryToken babyBearModulus :=
  { token with time := (1, 0) }

private def boundaryNative : Delegation.Row babyBearModulus := ⟨.blakeG, boundaryRow⟩
private def boundaryData : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [boundaryNative]
  initial := data.initial.map retimeSeed
  terminal := boundaryNative.memorySteps.map Prod.snd

private theorem boundaryAccepted : Delegation.MemoryAccepted boundaryData := by
  constructor
  · intro actual member
    simp only [boundaryData, List.mem_singleton] at member
    subst actual
    exact Verification.holds_append boundaryCore boundaryClocks
  · have reads : boundaryData.steps.map Prod.fst = boundaryData.initial := by decide
    have writes : boundaryData.steps.map Prod.snd = boundaryData.terminal := by rfl
    rw [reads, writes]
    exact List.perm_append_comm

private theorem boundaryMemory : Delegation.BoundaryMemoryInputs boundaryData before cells := by
  have original := Delegation.Proofs.boundary_image interface.publicState.toBoundaryInputs.toNativeInputs
  refine ⟨⟨?_, ?_⟩, interface.publicState.distinct, ?_, ?_⟩
  · simpa only [boundaryData, List.map_map, Function.comp_def, retimeSeed] using original.addresses
  · intro token member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨cell, tracked, value, code, read, word⟩ := original.values source sourceMember
    exact ⟨cell, tracked, value, code, read, word⟩
  · intro token member
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
    change 1 < timestampBase ∧ 0 < timestampBase
    decide
  · intro actual member
    simp only [boundaryData, List.mem_singleton] at member
    subst actual
    decide

theorem native_operation_with_nonzero_seeds :
    (∀ token ∈ boundaryData.initial, token.time = (1, 0)) ∧
    Delegation.MemoryExecution boundaryData before cells ∧
    Blake2G.spec (Blake2G.Native.input boundaryRow) (Blake2G.Native.output boundaryRow) := by
  have operations : Delegation.Proofs.BoundaryOperationInputs boundaryData before cells
      (fun _ => Vector.replicate 6 0) := by
    refine ⟨boundaryMemory.toBoundaryInputs, rfl, ?_, ?_⟩
    all_goals intro actual member family
    all_goals simp only [boundaryData, List.mem_singleton] at member
    all_goals subst actual; cases family
  have aligned : ∀ cell ∈ cells, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  have result := Blake2G.Native.Proofs.operation_execution_at_boundary (by decide) (by decide)
    boundaryAccepted operations aligned
  refine ⟨?_, result.1, result.2 boundaryNative (by simp [boundaryData]) rfl⟩
  intro token member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem incomplete_prefix_rejected (upper : Nat) :
    ¬ Blake2G.WindowInputs data before cells false 6 upper := by
  intro inputs
  have count : (data.prefixRows 6).length = 1 := by decide
  have complete := inputs.prefixComplete
  rw [count] at complete
  contradiction

theorem partial_request_changes_control :
    ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
      events.Perm (data.steps.map transferEvent) ∧ SailHistory cells events before after ∧
      (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨events, after, permutation, _, history, _, _, _, final⟩ := native_operation_execution.1
  let token := native.writeToken Blake2G.importedConstraintsMemoryPorts[8]
  have member : token ∈ data.terminal := by decide
  obtain ⟨cell, _, address, read⟩ := final token member
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have value : memoryWord token.value = 1 := by
    norm_num [token, memoryWord, native, Delegation.Row.writeToken,
      Blake2G.importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code,
      pairCode, row, Arithmetic.Word.value, Arithmetic.Word.toBitVec, Arithmetic.limbBase,
      ZMod.val_one, ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]
    rfl
  exact ⟨events, after, permutation, history, by simpa only [value] using read⟩

theorem complete_request_controls_repeat :
    Blake2G.controlAt false 160 = Blake2G.controlAt false 0 ∧
      Blake2G.controlAt true 112 = Blake2G.controlAt true 0 := by decide

theorem native_window_from_retained_seeds :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess)
      (atCut : Reference.RiscV.Sail.State),
      tokens.Perm boundaryData.terminal ∧ events.Perm (boundaryData.steps.map transferEvent) ∧
      SailHistory cells events before atCut ∧
      (∀ token ∈ tokens, token.time = (6, 0) ∧ token.word.Bounded) ∧
      Delegation.BoundaryImage tokens atCut cells := by
  have family : ∀ row ∈ boundaryData.rows, row.family = .blakeG := by
    intro actual member
    simp only [boundaryData, List.mem_singleton] at member
    subst actual
    rfl
  have rules := Blake2G.Proofs.memory_rules (by decide) (by decide) boundaryAccepted family (by rfl)
  have aligned : ∀ cell ∈ cells, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  obtain ⟨start, _, earlier, _, atStart, _, facts, _, permutation, _, history, _, inputs, _⟩ :=
    Delegation.Proofs.native_span_window_at_boundary (by decide) boundaryAccepted
      boundaryMemory.toBoundaryInputs rules aligned 6 6
  have steps : Trace.Proofs.Transfer.beforeSteps (Delegation.Proofs.transferData boundaryData) 6 =
      boundaryData.steps := by decide
  have reads : boundaryData.steps.map Prod.fst = boundaryData.initial := by decide
  have writes : boundaryData.steps.map Prod.snd = boundaryData.terminal := by rfl
  have matching := facts.matching
  change (boundaryData.initial ++
    (Trace.Proofs.Transfer.beforeSteps (Delegation.Proofs.transferData boundaryData) 6).map Prod.snd).Perm
    (start ++ (Trace.Proofs.Transfer.beforeSteps (Delegation.Proofs.transferData boundaryData) 6).map Prod.fst) at matching
  rw [steps, reads, writes] at matching
  have exactBoundary : start.Perm boundaryData.terminal :=
    ((List.perm_append_left_iff boundaryData.initial).mp
      (matching.trans List.perm_append_comm)).symm
  refine ⟨start, earlier, atStart, exactBoundary, ?_, history, ?_, Delegation.Proofs.boundary_image inputs⟩
  · simpa only [steps] using permutation
  · intro token member
    refine ⟨?_, inputs.words token member⟩
    have terminal := exactBoundary.mem_iff.mp member
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp terminal
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp included
    change ((rawPair boundaryRow boundaryNative.columns.invocation).1 + port.clock.offset,
      (rawPair boundaryRow boundaryNative.columns.invocation).2) = (6, 0)
    rw [Delegation.Proofs.port_offset boundaryNative (by simpa using present)]
    decide

end Tests.Blake2GMemory
