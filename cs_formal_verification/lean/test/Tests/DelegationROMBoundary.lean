import Slop.Sail.ResetState
import Tests.BigintMemory
import Tests.DelegationCaller
import Tests.DelegationOperationEffects
import Slop.Delegation.RequestTrace
import Human.Helpers.Memory.Native
import Slop.Trace.ROMView

namespace Tests.DelegationROMBoundary
open Airbender Delegation Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def assignment (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5 else if column = 4 ∨ column = 38 then 0 else Tests.BigintMemory.row column
private def worker : Delegation.Row babyBearModulus := ⟨.bigint, assignment⟩
private def workers : MemoryData babyBearModulus where
  setup := modeledSetup Keccak.Controller.rows
  rows := [worker]
  initial := worker.memorySteps.map Prod.fst
  terminal := worker.memorySteps.map Prod.snd
private def callerAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 35 then 4 else Tests.DelegationCaller.assignment .bigint column
private def caller : Trace.Row babyBearModulus PooledFamily := ⟨.addSub, callerAssignment⟩
private noncomputable def data : Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [caller]
    rom := ⟨{ name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩
    initial := caller.start
    terminal := caller.finish
    initialMemory := (Cell.register 0).initialToken 0 :: workers.initial
    terminalMemory := Caller.destinationToken callerAssignment :: workers.terminal }
  workers := workers
  program := [Tests.DelegationCaller.entry .bigint]

private def cells : List Cell := [.register 0, .register 10] ++
  (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4 * i))) ++ [.register 11] ++
  (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (32 + 4 * i))) ++ [.register 12]
private noncomputable def shadow : State where
  regs := resetMachine.regs.insert .x10 (0 : BitVec 32)
    |>.insert .x11 (32 : BitVec 32) |>.insert .x12 (128 : BitVec 32)
  mem := (List.range 64).foldl (fun memory i => memory.insert i (0 : BitVec 8))
    (Std.ExtHashMap.emptyWithCapacity)
  tags := ()
  cycleCount := 0
  sailOutput := #[]
private noncomputable def before : State := wordWriteState shadow 0 (Tests.DelegationCaller.entry .bigint).bits

private theorem airbender_before : Configured before := by
  configured_fixture [before, wordWriteState, shadow]

private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    (Bigint.importedConstraints Bigint.setupTable) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignment, Tests.BigintMemory.row, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨⟨0, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨262144, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1310720, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1312768, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1316864, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1325056, by decide⟩, ?_⟩; decide +kernel)

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    Bigint.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 40 := by simpa only [Bigint.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

theorem worker_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (worker.constraints workers.setup) :=
  Verification.holds_append core clocks

private def statePort : MemoryPort := worker.ports[1]'(by decide +kernel)

private theorem accepted : Caller.SharedMemoryAccepted data := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · intro row member
      have same : row = caller := List.mem_singleton.mp member
      subst row
      let original := Tests.DelegationOperationEffects.sharedData.machine.rows[0]'(by decide +kernel)
      exact Tests.DelegationOperationEffects.sharedAccepted.constraints original (List.mem_singleton_self _)
    · intro row member
      have same : row = caller := List.mem_singleton.mp member
      subst row
      decide +kernel
    · exact List.Perm.swap _ _ []
    · intro row member
      have same : row = caller := List.mem_singleton.mp member
      subst row
      change ∃ i : Fin 1, Caller.nativeQuery callerAssignment = Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
      exact ⟨0, by decide +kernel⟩
    · intro row member
      have same : row = worker := List.mem_singleton.mp member
      subst row
      exact worker_constraints
    · intro row member
      have same : row = worker := List.mem_singleton.mp member
      subst row
      decide +kernel
    · have equal : data.calls = data.fulfillments := by decide +kernel
      rw [← equal]
      exact List.perm_append_comm
  · decide +kernel

private theorem inputs : Caller.RequestInputs data before [0] := by
  constructor
  · have bytes : (Cell.ram 0).read before = .ok (Tests.DelegationCaller.entry .bigint).bits before :=
      written_word_read shadow 0 _
    have decoded : Airbender.Reference.RiscV.Sail.decodeOnReset (Tests.DelegationCaller.entry .bigint).bits = some (Tests.DelegationCaller.entry .bigint).instruction :=
      Tests.DelegationCaller.original_decoder .bigint
    have fields : Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
        some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
    simp only [Caller.programImage, programImageWith, List.mapM_cons, List.mapM_nil,
      programEntryWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · decide +kernel
  · exact airbender_before

theorem native_shadow_initialization : initialImage shadow cells = some data.machine.initialMemory := by
  have x10 : (Cell.register 10).read shadow = .ok 0 shadow := by
    apply read_register
    simp [shadow, Std.ExtDHashMap.get?_insert]
  have x11 : (Cell.register 11).read shadow = .ok 32 shadow := by
    apply read_register
    simp [shadow, Std.ExtDHashMap.get?_insert]
  have x12 : (Cell.register 12).read shadow = .ok 128 shadow := by
    apply read_register
    simp [shadow]
  norm_num [cells, List.range_succ, initialImage, List.mapM_cons, List.mapM_nil, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get,
    EStateM.pure, shadow, List.range_succ, Std.ExtHashMap.getElem_insert,
    Cell.initialToken, data, workers, worker, Delegation.Row.memorySteps,
    Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts, readToken,
    MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, assignment, Tests.BigintMemory.row, Word.ofBitVec, limbBase]
  all_goals decide +kernel

theorem native_caller_worker_matching : Caller.SharedMemoryAccepted data := accepted

theorem public_request_binding : Caller.RequestBinding data before :=
  Caller.Proofs.request_binding_checks (by decide +kernel) (by decide +kernel) (by decide +kernel)
    accepted.toRequestChecks inputs

theorem supported_copy_mode : assignment 66 = 1 ∧ assignment 55 = 128 ∧ assignment 56 = 0 := by
  decide +kernel

theorem worker_accesses_rom : statePort ∈ worker.ports ∧
    statePort.address.code assignment = (Cell.ram 0).addressCode ∧
    Trace.ROMView.shadow (statePort.address.code assignment) := by
  decide +kernel

theorem public_rom_word_nonzero : (Cell.ram 0).read before =
    .ok (Tests.DelegationCaller.entry .bigint).bits before ∧ (Tests.DelegationCaller.entry .bigint).bits ≠ 0 :=
  ⟨written_word_read shadow 0 _, by decide +kernel⟩

theorem worker_token_changes_under_rom_view :
    Trace.ROMView.token before (readToken assignment statePort) ≠ readToken assignment statePort := by
  have bytes : (Cell.ram 0).read before = .ok (Tests.DelegationCaller.entry .bigint).bits before :=
    written_word_read shadow 0 _
  have physical := Trace.ROMView.public_word_read bytes
  have address : (readToken assignment statePort).address = (Cell.ram 0).addressCode := by decide +kernel
  intro equal
  have value := congrArg MemoryToken.value equal
  simp only [Trace.ROMView.token, address, Trace.ROMView.shadow_ram, show (0 : BitVec 32).toNat < ROM.limit by decide,
    ite_true, physical] at value
  have impossible : ¬ Nat.pair (Word.ofBitVec (Tests.DelegationCaller.entry .bigint).bits).lo
      (Word.ofBitVec (Tests.DelegationCaller.entry .bigint).bits).hi = (readToken assignment statePort).value := by
    decide +kernel
  exact impossible value

theorem machine_only_rom_lift_breaks_matching :
    ¬ ((data.machine.initialMemory.map (Trace.ROMView.token before)) ++ data.sharedSteps.map Prod.snd).Perm
      ((data.machine.terminalMemory.map (Trace.ROMView.token before)) ++ data.sharedSteps.map Prod.fst) := by
  intro matching
  have accessed : readToken assignment statePort ∈ data.sharedSteps.map Prod.fst := by decide +kernel
  have produced := matching.mem_iff.mpr (List.mem_append.mpr (Or.inr accessed))
  rcases List.mem_append.mp produced with initial | written
  · obtain ⟨token, present, same⟩ := List.mem_map.mp initial
    have address := congrArg MemoryToken.address same
    simp only [Trace.ROMView.token_address] at address
    have only : ∀ token ∈ data.machine.initialMemory,
        token.address = (readToken assignment statePort).address → token = readToken assignment statePort := by
      decide +kernel
    have selected := only token present address
    subst token
    exact worker_token_changes_under_rom_view same
  · obtain ⟨edge, present, same⟩ := List.mem_map.mp written
    have time := congrArg MemoryToken.time same
    have noZero : ∀ edge ∈ data.sharedSteps, edge.2.time ≠ (0, 0) := by decide +kernel
    exact noZero edge present time

end Tests.DelegationROMBoundary
