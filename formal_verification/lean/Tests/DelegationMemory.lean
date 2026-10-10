import Tests.KeccakTheta
import Airbender.Review.Delegation.Theorems
import Airbender.Proofs.Keccak.CallHistory
import Airbender.Proofs.Delegation.AtomicHistory
import Airbender.Proofs.Keccak.StateTransport

namespace Tests.DelegationMemory
open Airbender Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def row (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5
  else if column = 14 then 64
  else if 222 ≤ column ∧ column < 264 ∧ (column - 222) % 3 = 2 then 1
  else Tests.KeccakTheta.row column

private def native : Delegation.Row babyBearModulus := ⟨.keccak, row⟩

theorem native_invocation_convention :
    (decodeTimestamp row Keccak.importedConstraintsDelegationColumns.invocation).lo % 4 = 1 ∧
    (decodeTimestamp row Keccak.importedConstraintsDelegationColumns.invocation).lo + 2 < timestampBase := by
  decide

theorem native_write_convention :
    (timeOfPair (native.writeToken Keccak.importedConstraintsMemoryPorts[0]).time).value = 7 ∧
    (timeOfPair (native.writeToken Keccak.importedConstraintsMemoryPorts[0]).time).value % 4 = 3 := by
  decide

theorem oracle_debug_assert_rejects_invocation :
    (decodeTimestamp row Keccak.importedConstraintsDelegationColumns.invocation).value % 4 ≠ 3 := by
  decide

private theorem queries_unchanged (i : Fin 42) :
    ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup)).get
      ⟨i.val, by rw [Keccak.lookup_count]; exact i.isLt⟩).entry.map
      (Expression.eval (Verification.environment row)) =
    ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup)).get
      ⟨i.val, by rw [Keccak.lookup_count]; exact i.isLt⟩).entry.map
      (Expression.eval (Verification.environment Tests.KeccakTheta.row)) := by
  fin_cases i
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals first | change j < 1 at hj | change j < 8 at hj
  all_goals interval_cases j
  all_goals simp only [Vector.getElem_map]
  all_goals decide +kernel +revert

private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraints Tests.KeccakTheta.setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have old := Verification.lookup_of_holds Tests.KeccakTheta.satisfies ⟨i, hi⟩
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    have same := queries_unchanged ⟨i, bound⟩
    simp only [List.get_eq_getElem] at same old
    simp only [Lookup.Contains, Verification.environment] at old ⊢
    exact Eq.mp (congrArg (fun entry =>
      ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup))[i]).table.Contains
        #[] entry) same.symm) old

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Keccak.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 30 := by simpa only [Keccak.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, row, Tests.KeccakTheta.row,
      Trace.timestampBase, ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

private def setup : Delegation.Setup babyBearModulus :=
  ⟨{ name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False }, Tests.KeccakTheta.setup⟩

private def cells : List Cell :=
  [.register 10, .register 11, .ram 4194304, .ram 4194308, .ram 4194344, .ram 4194348, .ram 4194384, .ram 4194388,
    .ram 4194424, .ram 4194428, .ram 4194464, .ram 4194468, .ram 4194504, .ram 4194508]

private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x10 (3 : BitVec 32)
    |>.insert .x11 (4194304 : BitVec 32)
  mem := (Std.ExtHashMap.emptyWithCapacity)
    |>.insert 4194304 (255 : BitVec 8)
    |>.insert 4194305 (255 : BitVec 8)
    |>.insert 4194306 (255 : BitVec 8)
    |>.insert 4194307 (255 : BitVec 8)
    |>.insert 4194308 (255 : BitVec 8)
    |>.insert 4194309 (255 : BitVec 8)
    |>.insert 4194310 (255 : BitVec 8)
    |>.insert 4194311 (255 : BitVec 8)
    |>.insert 4194344 (255 : BitVec 8)
    |>.insert 4194345 (255 : BitVec 8)
    |>.insert 4194346 (255 : BitVec 8)
    |>.insert 4194347 (255 : BitVec 8)
    |>.insert 4194348 (255 : BitVec 8)
    |>.insert 4194349 (255 : BitVec 8)
    |>.insert 4194350 (255 : BitVec 8)
    |>.insert 4194351 (255 : BitVec 8)
    |>.insert 4194384 (255 : BitVec 8)
    |>.insert 4194385 (255 : BitVec 8)
    |>.insert 4194386 (255 : BitVec 8)
    |>.insert 4194387 (255 : BitVec 8)
    |>.insert 4194388 (255 : BitVec 8)
    |>.insert 4194389 (255 : BitVec 8)
    |>.insert 4194390 (255 : BitVec 8)
    |>.insert 4194391 (255 : BitVec 8)
    |>.insert 4194424 (255 : BitVec 8)
    |>.insert 4194425 (255 : BitVec 8)
    |>.insert 4194426 (255 : BitVec 8)
    |>.insert 4194427 (255 : BitVec 8)
    |>.insert 4194428 (255 : BitVec 8)
    |>.insert 4194429 (255 : BitVec 8)
    |>.insert 4194430 (255 : BitVec 8)
    |>.insert 4194431 (255 : BitVec 8)
    |>.insert 4194464 (255 : BitVec 8)
    |>.insert 4194465 (255 : BitVec 8)
    |>.insert 4194466 (255 : BitVec 8)
    |>.insert 4194467 (255 : BitVec 8)
    |>.insert 4194468 (255 : BitVec 8)
    |>.insert 4194469 (255 : BitVec 8)
    |>.insert 4194470 (255 : BitVec 8)
    |>.insert 4194471 (255 : BitVec 8)
    |>.insert 4194504 (1 : BitVec 8)
    |>.insert 4194505 (0 : BitVec 8)
    |>.insert 4194506 (0 : BitVec 8)
    |>.insert 4194507 (0 : BitVec 8)
    |>.insert 4194508 (0 : BitVec 8)
    |>.insert 4194509 (0 : BitVec 8)
    |>.insert 4194510 (0 : BitVec 8)
    |>.insert 4194511 (1 : BitVec 8)
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd

theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

private theorem initialized : initialImage before cells = some data.initial := by
  have x10 : Cell.read (.register 10) before = .ok 3 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) before = .ok 4194304 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x10, x11]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes,
    _root_.Sail.ArchSem.readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before,
    Std.ExtHashMap.getElem_insert, Cell.initialToken, data, native, Delegation.Row.memorySteps,
    Delegation.Row.ports, Keccak.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, row, Tests.KeccakTheta.row,
    Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
  all_goals decide

private theorem inputs : Delegation.MemoryInputs data before cells := by
  constructor
  · exact initialized
  · decide
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    decide

theorem native_memory_soundness : Delegation.MemorySoundness data :=
  Delegation.memory_soundness (by decide) accepted inputs

theorem native_pointer_preserved :
    (∀ actual ∈ data.rows, Keccak.statePointer actual.assignment = Arithmetic.Word.ofBitVec 4194304) ∧
    ∃ sink ∈ data.terminal, sink.address = (Cell.register 11).addressCode ∧
      sink.word = Arithmetic.Word.ofBitVec 4194304 := by
  apply Keccak.Proofs.pointer_history (by decide) accepted inputs
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    rfl
  · simp [cells]
  · apply Reference.RiscV.Sail.read_register
    simp [before]

theorem native_sail_execution : Delegation.MemoryExecution data before cells := by
  apply Delegation.native_memory_execution (by decide) accepted inputs
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Cell.Aligned]

theorem native_grouped_call :
    ∃ after, Delegation.Proofs.GroupedSailHistory cells
      (fun actual : Delegation.Row babyBearModulus => actual.memorySteps.map transferEvent)
      [native] before after ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (Trace.Proofs.memoryWord token.value) after := by
  obtain ⟨events, after, permutation, ordered, history, _, _, _, terminal⟩ := native_sail_execution
  refine ⟨after, ?_, terminal⟩
  apply Delegation.Proofs.grouped_history (fun actual => Keccak.callWriteTime actual + 1) _
    (by simp) ordered ?_ ?_ history
  · simpa only [data, Delegation.MemoryData.steps, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_flatMap] using permutation
  · intro actual member event included
    simp only [List.mem_singleton] at member
    subst actual
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp included
    change edge ∈ native.ports.toList.map (fun port => (readToken native.assignment port, native.writeToken port)) at present
    obtain ⟨port, present, same⟩ : ∃ port ∈ native.ports.toList,
        (readToken native.assignment port, native.writeToken port) = edge := List.mem_map.mp present
    rw [← same]
    exact Keccak.Proofs.call_event_time native (by simpa only [Array.mem_toList_iff] using present)

theorem native_atomic_reads_and_writes :
    ∃ after, ∀ port ∈ native.ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code native.assignment ∧
      cell.read before = .ok (Trace.Proofs.memoryWord (port.readCode native.assignment)) before ∧
      cell.read after = .ok (Trace.Proofs.memoryWord (port.writeCode native.assignment)) after := by
  obtain ⟨after, grouped, _⟩ := native_grouped_call
  cases grouped with
  | @cons actual rest start middle finish events past permutation current =>
    cases past with
    | nil =>
      have aligned : ∀ cell ∈ cells, cell.Aligned := by
        intro cell member
        simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [Cell.Aligned]
      have readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before := by
        intro cell member
        obtain ⟨_, _, value, read, _⟩ := Trace.Proofs.image_cell_source initialized cell member
        exact ⟨value, read⟩
      exact ⟨after, Delegation.Proofs.row_atomic_observations (by decide) accepted inputs
        (by simp [data]) current permutation aligned readable⟩

theorem native_word_bounds :
    (∀ actual ∈ data.rows, ∀ port ∈ actual.ports,
      (readToken actual.assignment port).word.Bounded) ∧
    (∀ actual ∈ data.rows, ∀ port ∈ actual.ports, (actual.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) := by
  apply Keccak.Memory.native_value_bounds (by decide) accepted
    (control := Tests.KeccakTheta.control)
  constructor
  · exact inputs
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    rfl
  · rfl
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    decide

theorem native_physical_lanes :
    ∃ after, ∀ lane : Fin 6,
      let address := (4194304 : BitVec 32) + BitVec.ofNat 32 (8 * (row (7 + lane.val)).val)
      Keccak.Native.readLane row lane = Delegation.Proofs.ramLane before address ∧
        Keccak.Native.writtenLane row lane = Delegation.Proofs.ramLane after address := by
  obtain ⟨after, ports⟩ := native_atomic_reads_and_writes
  have addresses := Keccak.Proofs.addresses (p := babyBearModulus) (by decide) (by decide)
    (control := Tests.KeccakTheta.control)
    (by intro key lane; fin_cases lane <;> norm_num [Tests.KeccakTheta.control])
    (by norm_num [Keccak.statePointer, row, Tests.KeccakTheta.row, Arithmetic.Word.Bounded,
      Arithmetic.limbBase, babyBearModulus, ZMod.val_ofNat, ZMod.val_natCast]) core
  have member : native ∈ data.rows := by simp [data]
  have reads := native_word_bounds.1 native member
  have writes := native_word_bounds.2.1 native member
  have observed : ∀ port ∈ native.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code row ∧
        cell.read before = .ok (Trace.Proofs.memoryWord (port.readCode row)) before ∧
        cell.read after = .ok (Trace.Proofs.memoryWord (port.writeCode row)) after := by
    intro port present
    obtain ⟨cell, _, code, read, written⟩ := ports port present
    exact ⟨cell, code, read, written⟩
  refine ⟨after, ?_⟩
  intro lane
  have result := Keccak.Proofs.native_lane_observations addresses reads writes observed lane
  have pointer : (Keccak.statePointer row).toBitVec = 4194304 := by decide
  rw [pointer] at result
  exact result

private def sharedData : Delegation.MemoryData babyBearModulus :=
  { data with setup := Delegation.modeledSetup Tests.KeccakTheta.control }

theorem shared_operation_memory : Delegation.MemorySoundness sharedData ∧
    Delegation.WordBounds sharedData := by
  apply Delegation.operation_memory_soundness (by decide) (by decide)
    (before := before) (cells := cells) (control := Tests.KeccakTheta.control)
  · constructor
    · intro actual member
      simp only [sharedData, data, List.mem_singleton] at member
      subst actual
      exact Verification.holds_append core clocks
    · exact List.perm_append_comm
  · constructor
    · exact ⟨inputs.initialization, inputs.distinct, inputs.clockRoom⟩
    · rfl
    · intro actual member family
      simp only [sharedData, data, List.mem_singleton] at member
      subst actual
      cases family
    · intro actual member _
      simp only [sharedData, data, List.mem_singleton] at member
      subst actual
      decide

end Tests.DelegationMemory
