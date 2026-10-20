import Tests.DelegationOperationEffects
import Slop.Final.Circuits.AddSub.CallerTheorems
import Slop.Final.Trace.Delegation.CallerTheorems

namespace Tests.DelegationMixedMemory
open Airbender Delegation Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

private abbrev base := Tests.DelegationOperationEffects.sharedData
private abbrev cells := Tests.DelegationOperationEffects.sharedCells
private def before : State := wordWriteState Tests.DelegationOperationEffects.before 4 0x00160613
private def program : List PooledProgramEntry := [
  ⟨4, 0x00160613, .ITYPE (1, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.addSub, 12, 0, 12, ⟨1, 0⟩, 1, 0⟩⟩]
private def arithmetic (value : Nat) : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 19 | 35 => 8
  | 21 | 5 | 7 => 12
  | 4 | 8 | 10 | 42 | 43 | 44 => 1
  | 23 => 7
  | 27 => 6
  | 25 => value
  | 33 => value + 1
  | _ => 0
private def ordinary (value : Nat) : Trace.Row babyBearModulus PooledFamily :=
  ⟨.addSub, arithmetic value⟩
private def terminal (value : Nat) : List (MemoryToken babyBearModulus) :=
  base.machine.terminalMemory.map fun token =>
    if token.address = (Cell.register 0).addressCode then
      ⟨token.address, (9, 0), 0⟩
    else if token.address = (Cell.register 12).addressCode then
      ⟨token.address, (10, 0), Nat.pair (value + 1) 0⟩
    else token
private def data (value : Nat) : Caller.RequestTrace babyBearModulus :=
  { base with machine := { base.machine with
    rows := ordinary value :: base.machine.rows
    terminal := (ordinary value).finish
    terminalMemory := terminal value
    rom := ⟨ROM.table cells base.machine.initialMemory,
      Verification.subwordTable (ROM.words before)⟩ } }

private theorem local_constraints (value : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic value.val)) AddSub.clockConstraints := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · fin_cases value <;> decide +kernel
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 6 := by simpa only [AddSub.lookup_count] using bound
      interval_cases i
      all_goals apply Verification.range16_contains
      all_goals fin_cases value <;> decide +kernel
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [AddSub.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals fin_cases value <;> decide +kernel

private theorem checks : Caller.RequestChecks (data 0) := by
  constructor
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact local_constraints 0
    · have family := (Caller.Proofs.caller_member (data := base)
        (Tests.DelegationOperationEffects.sharedAccepted.callerRows.symm ▸ member)).2
      simpa only [Trace.Row.constraints, family, CircuitLayout.constraints] using
        Tests.DelegationOperationEffects.sharedAccepted.constraints row member
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    · exact Tests.DelegationOperationEffects.sharedAccepted.active row member
  · change ([base.machine.initial] ++ [(ordinary 0).finish, base.machine.terminal]).Perm
      ([(ordinary 0).finish, base.machine.terminal] ++ [base.machine.initial])
    exact List.perm_append_comm
  · exact Tests.DelegationOperationEffects.sharedAccepted.decoded
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerConstraints
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerActive
  · exact Tests.DelegationOperationEffects.sharedAccepted.requests

private theorem accepted : Caller.MixedMemoryAccepted (data 0) program := by
  refine ⟨checks, ?_, ?_⟩
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · change ∃ i : Fin 1, (ordinary 0).decoderQuery = (program.get i).query
      exact ⟨0, by decide +kernel⟩
    · have caller : row ∈ (data 0).callers := member
      exact False.elim (noncaller caller)
  · decide +kernel

private theorem initialization : initialImage before cells = some (data 0).machine.initialMemory := by
  apply Trace.Proofs.image_frame (before := Tests.DelegationOperationEffects.before)
    (after := before) (cells := cells) (tokens := base.machine.initialMemory)
    Tests.DelegationOperationEffects.sharedInputs.initialization
  intro cell member value read
  cases cell with
  | register index =>
    change run (SailRV32.Functions.rX_bits (.Regidx index)) Tests.DelegationOperationEffects.before =
      .ok value Tests.DelegationOperationEffects.before at read
    change run (SailRV32.Functions.rX_bits (.Regidx index)) before = .ok value before
    exact rX_register_frame (before := Tests.DelegationOperationEffects.before) (after := before)
      (value := value) (by dsimp only [before, wordWriteState]) index read
  | ram address =>
    have lower : 8 ≤ address.toNat := by
      simp [cells, Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
      rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
      all_goals interval_cases i <;> decide
    exact written_word_disjoint 4 _ (Or.inr lower) read

private theorem inputs : Caller.MixedMemoryInputs (data 0) program before [0] [4] cells := by
  refine ⟨?_, ?_, rfl, rfl, Tests.DelegationOperationEffects.sharedInputs.tables,
    Tests.DelegationOperationEffects.sharedInputs.rounds⟩
  · constructor
    · constructor
      · have bytes : (Cell.ram 0).read before = .ok (Tests.DelegationCaller.entry .bigint).bits before :=
          written_word_disjoint 4 _ (Or.inl (by decide))
            (written_word_read Tests.BigintMemory.before 0 _)
        have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) before =
            .ok (Tests.DelegationCaller.entry .bigint).instruction before :=
          Tests.DelegationCaller.original_decoder .bigint before
        have fields : Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
            some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
        simp only [Caller.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
          programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
        rfl
      · exact Tests.DelegationOperationEffects.sharedInputs.publicProgram.initialClock
      · exact Tests.DelegationOperationEffects.sharedInputs.publicProgram.initialAligned
    · exact initialization
    · exact Tests.DelegationOperationEffects.sharedInputs.distinct
    · exact Tests.DelegationOperationEffects.sharedInputs.aligned
  · have bytes : (Cell.ram 4).read before = .ok 0x00160613 before := written_word_read _ _ _
    have decoded : run (SailRV32.Functions.encdec_backwards 0x00160613) before =
        .ok (.ITYPE (1, .Regidx 12, .Regidx 12, .ADDI)) before := by with_unfolding_all rfl
    have fields : pooledDecoderFields (.ITYPE (1, .Regidx 12, .Regidx 12, .ADDI)) =
        some program[0].data := by with_unfolding_all rfl
    simp only [pooledProgramImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl

theorem shared_machine_worker_effects : Caller.MixedMemoryEffects (data 0) before cells :=
  Caller.mixed_memory_soundness accepted inputs

theorem every_issued_worker_is_unique : ∀ row ∈ (data 0).callers,
    ∃! worker, worker ∈ (data 0).workers.rows ∧
      Requests.fulfillment worker = Requests.caller row.assignment :=
  fun _ member => Caller.Proofs.unique_issued_worker shared_machine_worker_effects.requests member

theorem issued_worker_schedule : Caller.WorkerSchedule (data 0) :=
  Caller.worker_schedule_soundness (by norm_num [timestampBase, babyBearModulus])
    (by decide +kernel) (by decide +kernel) checks inputs.publicProgram

theorem copy_call_native_slot : ∃ caller ∈ (data 0).callers, ∃ worker ∈ (data 0).workers.rows,
    Caller.WorkerSlot caller worker ∧ Caller.startClock caller = 4 ∧
    (decodeTimestamp worker.assignment worker.columns.invocation).value = 5 ∧
    (∀ port ∈ worker.ports, (timeOfPair (worker.writeToken port).time).value = 7) ∧
    Caller.finishClock caller = 8 := by
  let caller := base.machine.rows[0]'(by decide +kernel)
  have member : caller ∈ (data 0).callers := by
    change caller ∈ [caller]
    exact List.mem_singleton_self caller
  have start : Caller.startClock caller = 4 := by decide +kernel
  obtain ⟨worker, matched, _⟩ := issued_worker_schedule.callers caller member
  refine ⟨caller, member, worker, matched.1, matched.2.2, start, ?_, ?_, ?_⟩
  · simpa only [start] using matched.2.2.invocation
  · intro port present
    simpa only [start] using matched.2.2.writes port present
  · simpa only [start] using matched.2.2.finish

theorem dependent_control_read :
    (readToken (arithmetic 0) AddSub.importedConstraintsMemoryPorts[0]).word = ⟨0, 0⟩ ∧
    (writeToken AddSub.importedConstraintsTraceColumns (arithmetic 0)
      AddSub.importedConstraintsMemoryPorts[2]).word = ⟨1, 0⟩ ∧
    (Cell.register 12).initialToken (p := babyBearModulus) 128 ∈ (data 0).machine.initialMemory := by
  decide +kernel

theorem actual_terminal_control : ∃ after : State,
    (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨_, after, _, _, _, final⟩ := shared_machine_worker_effects.execution
  have token : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus) ∈
      (data 0).machine.terminalMemory := by decide +kernel
  obtain ⟨cell, _, code, read⟩ := final _ token
  change cell.addressCode = (Cell.register 12).addressCode at code
  have equal := Trace.Proofs.cell_address_injective code
  subst cell
  have value : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus).word.toBitVec = 1 := by decide +kernel
  exact ⟨after, by simpa only [value] using read⟩

theorem fabricated_read_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic 1)) AddSub.clockConstraints := local_constraints 1

theorem fabricated_read_breaks_joint_matching : ¬Caller.MixedMemoryAccepted (data 1) program := by
  intro bad
  have missing : ¬((data 1).machine.initialMemory ++ (data 1).mixedSteps.map Prod.snd).Perm
      ((data 1).machine.terminalMemory ++ (data 1).mixedSteps.map Prod.fst) := by decide +kernel
  exact missing bad.memory

end Tests.DelegationMixedMemory
