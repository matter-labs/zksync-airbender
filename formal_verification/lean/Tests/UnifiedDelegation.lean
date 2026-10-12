import Tests.DelegationCaller
import Tests.BigintMemory
import Tests.DelegationOperationEffects
import Airbender.Review.UnifiedReduced.Theorems
import Airbender.Review.UnifiedReduced.Setup

namespace Tests.UnifiedDelegation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def before (family : Delegation.Family) : State :=
  wordWriteState Tests.BigintMemory.before 0 (Tests.DelegationCaller.entry family).bits

private def assignmentWith (address : ZMod babyBearModulus) (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 30 then 4
  else if column = 32 then 8
  else if column = 4 ∨ column = 18 ∨ column = 129 ∨ column = 130 ∨
      column = 131 ∨ column = 132 ∨ column = 133 then 1
  else if column = 6 ∨ column = 38 then address else 0

private def assignment (family : Delegation.Family) := assignmentWith (Delegation.Requests.csr family)

private theorem public_image (family : Delegation.Family) :
    UnifiedReduced.Caller.programImage (before family) [0] = some [Tests.DelegationCaller.entry family] := by
  have bytes : (Cell.ram 0).read (before family) =
      .ok (Tests.DelegationCaller.entry family).bits (before family) :=
    written_word_read Tests.BigintMemory.before 0 (Tests.DelegationCaller.entry family).bits
  have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry family).bits)
      (before family) = .ok (Tests.DelegationCaller.entry family).instruction (before family) :=
    Tests.DelegationCaller.original_decoder family _
  have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry family).instruction =
      some (Tests.DelegationCaller.entry family).data := Tests.DelegationCaller.metadata family
  simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage,
    programImageRunWith, List.mapM_cons, List.mapM_nil, programEntryRunWith,
    bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem generic_core (state : State) (address : ZMod babyBearModulus) (addressBound : address.val < limbBase) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignmentWith address))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table state)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignmentWith, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains
       simpa [Expression.eval, assignmentWith] using addressBound)
    | (apply Verification.range16_contains
       simp [Expression.eval, assignmentWith]
       decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem core (family : Delegation.Family) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment family))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (before family))) :=
  generic_core (before family) _ (by cases family <;> decide +kernel)

private theorem timestamps (family : Delegation.Family) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment family)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases family <;> decide +kernel

theorem all_caller_forms_satisfy (family : Delegation.Family) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment family))
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.table (before family))) :=
  Verification.holds_append (core family) (timestamps family)

theorem original_public_caller_soundness (family : Delegation.Family) :
    UnifiedReduced.Caller.Binding (assignment family) (before family) [Tests.DelegationCaller.entry family] := by
  apply UnifiedReduced.Caller.soundness (by decide +kernel) (core family) (public_image family)
  change ∃ i : Fin 1, UnifiedReduced.decoderQuery (assignment family) =
    Delegation.Caller.query ([Tests.DelegationCaller.entry family].get i)
  refine ⟨0, ?_⟩
  cases family <;> decide +kernel

theorem caller_request_retains_full_csr (family : Delegation.Family) :
    (UnifiedReduced.Caller.request (assignment family)).csr = Delegation.Requests.csr family ∧
    31 < (UnifiedReduced.Caller.request (assignment family)).csr := by
  cases family <;> decide +kernel

private def truncated (family : Delegation.Family) := assignmentWith (Delegation.Requests.csr family % 32)

theorem truncated_csr_locally_satisfies (family : Delegation.Family) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (truncated family))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (before family))) :=
  generic_core (before family) _ (by cases family <;> decide +kernel)

theorem truncated_csr_rejected_by_public_decoder (family : Delegation.Family) :
    ¬ (UnifiedReduced.Caller.decoderTable (p := babyBearModulus) [Tests.DelegationCaller.entry family]).Contains
      #[] (UnifiedReduced.decoderQuery (truncated family)) := by
  change ¬ ∃ i : Fin 1, UnifiedReduced.decoderQuery (truncated family) =
    Delegation.Caller.query ([Tests.DelegationCaller.entry family].get i)
  intro ⟨i, equal⟩
  have field := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[3]) equal
  fin_cases i
  have impossible : ¬ (UnifiedReduced.decoderQuery (truncated family))[3] =
      (Delegation.Caller.query ([Tests.DelegationCaller.entry family].get 0))[3] := by
    cases family <;> decide +kernel
  exact impossible field

private def machineRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, assignment .bigint⟩
private def machine : UnifiedTrace babyBearModulus where
  rows := [machineRow]
  rom := UnifiedReduced.Setup.table (before .bigint)
  initial := machineRow.start
  terminal := machineRow.finish
  initialMemory := []
  terminalMemory := []
private def requests : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  ⟨machine, Tests.DelegationOperationEffects.sharedData.workers, [Tests.DelegationCaller.entry .bigint]⟩
private def worker : Delegation.Row babyBearModulus :=
  requests.workers.rows.get ⟨0, by decide +kernel⟩

private theorem requestChecks : UnifiedReduced.Caller.RequestChecks requests := by
  constructor
  · intro row member
    have same : row = machineRow := List.mem_singleton.mp member
    subst row
    exact all_caller_forms_satisfy .bigint
  · intro row member
    have same : row = machineRow := List.mem_singleton.mp member
    subst row
    decide +kernel
  · exact List.Perm.swap _ _ []
  · intro row member
    have same : row = machineRow := List.mem_singleton.mp (List.mem_filter.mp member).1
    subst row
    change ∃ i : Fin 1, UnifiedReduced.decoderQuery (assignment .bigint) =
      Delegation.Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
    exact ⟨0, by decide +kernel⟩
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerConstraints
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerActive
  · have equal : requests.calls = requests.fulfillments := by decide +kernel
    rw [← equal]
    exact List.perm_append_comm

private theorem requestInputs : UnifiedReduced.Caller.RequestInputs requests (before .bigint) [0] := by
  refine ⟨public_image .bigint, ?_, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · decide +kernel

theorem issued_copy_request : UnifiedReduced.Caller.RequestBinding requests (before .bigint) :=
  UnifiedReduced.Caller.request_soundness (by decide +kernel) (by decide +kernel) requestChecks requestInputs

theorem copy_inside_native_cycle :
    (decodeTimestamp worker.assignment worker.columns.invocation).value = 5 ∧
    (∀ port ∈ worker.ports, (timeOfPair (worker.writeToken port).time).value = 7) ∧
    Delegation.Caller.finishClock machineRow = 8 := by
  have included : machineRow ∈ requests.callers := by
    change machineRow ∈ [machineRow]
    exact List.mem_singleton_self _
  obtain ⟨matched, ⟨present, _, slot⟩, _⟩ := issued_copy_request.workers machineRow included
  have same : matched = worker := by
    change matched ∈ [worker] at present
    exact List.mem_singleton.mp present
  subst matched
  have initial : Delegation.Caller.startClock machineRow = 4 := by decide +kernel
  refine ⟨slot.invocation.trans (by rw [initial]), ?_, slot.finish.trans (by rw [initial])⟩
  intro port present
  exact (slot.writes port present).trans (by rw [initial])

theorem worker_family_from_public_bytes :
    ∃ entry ∈ requests.program,
      entry.SourceWith (before .bigint) Delegation.Caller.decoderFields ∧ worker.family = entry.data.family := by
  have included : machineRow ∈ requests.callers := by
    change machineRow ∈ [machineRow]
    exact List.mem_singleton_self _
  obtain ⟨matched, ⟨present, same, _⟩, _⟩ := issued_copy_request.workers machineRow included
  have chosen : matched = worker := by
    change matched ∈ [worker] at present
    exact List.mem_singleton.mp present
  subst matched
  obtain ⟨entry, present, source, csr⟩ := (issued_copy_request.callers machineRow included).instruction
  refine ⟨entry, present, source, Delegation.Caller.Proofs.csr_injective ?_⟩
  exact (congrArg Delegation.Requests.Request.csr same).trans csr

private theorem reject_matching (workers : List (Delegation.Requests.Request babyBearModulus))
    (left : (requests.calls.map Delegation.Requests.Request.issued ++ workers.map Delegation.Requests.Request.empty).count
      (Delegation.Requests.Request.issued (UnifiedReduced.Caller.request (assignment .bigint))) = 1)
    (right : (requests.calls.map Delegation.Requests.Request.empty ++ workers.map Delegation.Requests.Request.issued).count
      (Delegation.Requests.Request.issued (UnifiedReduced.Caller.request (assignment .bigint))) = 0) :
    ¬ Delegation.Requests.Matching requests.calls workers := by
  intro matching
  have count := matching.count_eq (Delegation.Requests.Request.issued (UnifiedReduced.Caller.request (assignment .bigint)))
  rw [left, right] at count
  contradiction

theorem missing_copy_worker_rejected : ¬ Delegation.Requests.Matching requests.calls [] :=
  reject_matching [] (by decide +kernel) (by decide +kernel)

private def wrongClockWorker : Delegation.Row babyBearModulus :=
  ⟨worker.family, fun column => if column = 1 then 9 else worker.assignment column⟩

theorem wrong_copy_clock_rejected :
    ¬ Delegation.Requests.Matching requests.calls [Delegation.Requests.fulfillment wrongClockWorker] :=
  reject_matching _ (by decide +kernel) (by decide +kernel)

private abbrev base := Tests.DelegationOperationEffects.sharedData
private abbrev cells := Tests.DelegationOperationEffects.sharedCells
private def mixedBefore : State := wordWriteState Tests.DelegationOperationEffects.before 4 0x00160613
private def mixedProgram : List UnifiedReduced.ProgramEntry := [
  ⟨4, 0x00160613, .ITYPE (1, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, ⟨1, 0⟩, 1, 0⟩⟩]
private def sharedAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 46 then 4 else assignment .bigint column
private def sharedCaller : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, sharedAssignment⟩
private def arithmetic (value : Nat) : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 30 => 8
  | 32 | 5 | 7 | 44 => 12
  | 4 | 8 | 11 | 129 | 130 | 131 | 132 | 133 => 1
  | 34 => 7
  | 40 => 6
  | 46 => 8
  | 36 | 48 => value
  | 50 => value + 1
  | _ => 0
private def ordinary (value : Nat) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, arithmetic value⟩
private def mixedTerminal (value : Nat) : List (MemoryToken babyBearModulus) :=
  base.machine.terminalMemory.map fun token =>
    if token.address = (Cell.register 0).addressCode then ⟨token.address, (9, 0), 0⟩
    else if token.address = (Cell.register 12).addressCode then ⟨token.address, (10, 0), Nat.pair (value + 1) 0⟩
    else token
private def mixedData (value : Nat) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [ordinary value, sharedCaller]
    rom := UnifiedReduced.Setup.table mixedBefore
    initial := sharedCaller.start
    terminal := (ordinary value).finish
    initialMemory := base.machine.initialMemory
    terminalMemory := mixedTerminal value }
  workers := base.workers
  program := [Tests.DelegationCaller.entry .bigint]

private theorem sharedCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment sharedAssignment) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table mixedBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, sharedAssignment, assignment, assignmentWith,
    Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem arithmeticCore (value : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic value.val))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table mixedBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, arithmetic, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (fin_cases value <;> decide +kernel)
    | (apply Verification.range16_contains; fin_cases value <;> decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem sharedTimestamps : FlatOperation.ConstraintsHoldFlat
    (Verification.environment sharedAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem arithmeticTimestamps (value : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic value.val)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases value <;> decide +kernel

private theorem mixedChecks : UnifiedReduced.Caller.RequestChecks (mixedData 0) := by
  constructor
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact Verification.holds_append (arithmeticCore 0) (arithmeticTimestamps 0)
    · have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append sharedCore sharedTimestamps
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    · have same := List.mem_singleton.mp member
      subst row
      decide +kernel
  · change ([sharedCaller.start] ++ [(ordinary 0).finish, sharedCaller.finish]).Perm
      ([(ordinary 0).finish, sharedCaller.finish] ++ [sharedCaller.start])
    exact List.perm_append_comm
  · intro row member
    have same : row = sharedCaller := List.mem_singleton.mp member
    subst row
    change ∃ i : Fin 1, UnifiedReduced.decoderQuery sharedAssignment =
      Delegation.Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
    exact ⟨0, by decide +kernel⟩
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerConstraints
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerActive
  · exact Tests.DelegationOperationEffects.sharedAccepted.requests

private theorem mixedAccepted : UnifiedReduced.Caller.MixedMemoryAccepted (mixedData 0) mixedProgram := by
  refine ⟨mixedChecks, ?_, ?_⟩
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · change ∃ i : Fin 1, (ordinary 0).decoderQuery = (mixedProgram.get i).query
      exact ⟨0, by decide +kernel⟩
    · have caller : row ∈ (mixedData 0).callers := member
      exact False.elim (noncaller caller)
  · decide +kernel

private theorem mixedInitialization : initialImage mixedBefore cells = some (mixedData 0).machine.initialMemory := by
  apply Trace.Proofs.image_frame (before := Tests.DelegationOperationEffects.before)
    (after := mixedBefore) (cells := cells) (tokens := base.machine.initialMemory)
    Tests.DelegationOperationEffects.sharedInputs.initialization
  intro cell member value read
  cases cell with
  | register index =>
    exact rX_register_frame (before := Tests.DelegationOperationEffects.before) (after := mixedBefore)
      (value := value) (by dsimp only [mixedBefore, wordWriteState]) index read
  | ram address =>
    have lower : 8 ≤ address.toNat := by
      simp [cells, Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
      rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
      all_goals interval_cases i <;> decide
    exact written_word_disjoint 4 _ (Or.inr lower) read

private theorem mixedInputs : UnifiedReduced.Caller.MixedMemoryInputs (mixedData 0) mixedProgram mixedBefore [0] [4] cells := by
  refine ⟨?_, ?_, mixedInitialization, Tests.DelegationOperationEffects.sharedInputs.distinct,
    Tests.DelegationOperationEffects.sharedInputs.aligned, rfl,
    Tests.DelegationOperationEffects.sharedInputs.tables, Tests.DelegationOperationEffects.sharedInputs.rounds⟩
  · constructor
    · have bytes : (Cell.ram 0).read mixedBefore = .ok (Tests.DelegationCaller.entry .bigint).bits mixedBefore :=
        written_word_disjoint 4 _ (Or.inl (by decide)) (written_word_read Tests.BigintMemory.before 0 _)
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) mixedBefore =
          .ok (Tests.DelegationCaller.entry .bigint).instruction mixedBefore :=
        Tests.DelegationCaller.original_decoder .bigint mixedBefore
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · decide +kernel
  · have bytes : (Cell.ram 4).read mixedBefore = .ok 0x00160613 mixedBefore := written_word_read _ _ _
    have decoded : run (SailRV32.Functions.encdec_backwards 0x00160613) mixedBefore =
        .ok (.ITYPE (1, .Regidx 12, .Regidx 12, .ADDI)) mixedBefore := by with_unfolding_all rfl
    have fields : UnifiedReduced.Mixed.decoderFields (.ITYPE (1, .Regidx 12, .Regidx 12, .ADDI)) =
        some mixedProgram[0].data := by with_unfolding_all rfl
    simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl

theorem shared_machine_worker_effects : UnifiedReduced.Caller.MixedMemoryEffects (mixedData 0) mixedBefore cells :=
  UnifiedReduced.Caller.mixed_memory_soundness mixedAccepted mixedInputs

theorem actual_terminal_control : ∃ after : State, (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨_, after, _, _, _, _, _, final⟩ := shared_machine_worker_effects.execution
  have token : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus) ∈
      (mixedData 0).machine.terminalMemory := by decide +kernel
  obtain ⟨cell, _, code, read⟩ := final _ token
  change cell.addressCode = (Cell.register 12).addressCode at code
  have equal := Trace.Proofs.cell_address_injective code
  subst cell
  have value : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus).word.toBitVec = 1 := by decide +kernel
  exact ⟨after, by simpa only [value] using read⟩

theorem actual_copy_call_boundaries : ∃ start finish after : State, ∃ newer : List MemoryAccess,
    (Cell.register 12).read start = .ok 128 start ∧
    (Cell.register 12).read finish = .ok 0 finish ∧
    Trace.Proofs.SailHistory cells newer finish after ∧
    (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨events, after, _, _, _, calls, _, final⟩ := shared_machine_worker_effects.execution
  have member : worker ∈ (mixedData 0).workers.rows := List.get_mem requests.workers.rows ⟨0, by decide +kernel⟩
  have live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker) := by decide +kernel
  obtain ⟨_, _, newer, start, finish, _, _, _, _, future, ports⟩ := calls worker member live
  let port := Bigint.importedConstraintsMemoryPorts[18]
  have present : port ∈ worker.ports := by decide +kernel
  obtain ⟨cell, _, code, read, written⟩ := ports port present
  have address : port.address.code worker.assignment = (Cell.register 12).addressCode := by decide +kernel
  have equal : cell = Cell.register 12 := Trace.Proofs.cell_address_injective (code.trans address)
  subst cell
  have old : (readToken worker.assignment port).word.toBitVec = 128 := by decide +kernel
  have result : (worker.writeToken port).word.toBitVec = 0 := by decide +kernel
  have token : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus) ∈
      (mixedData 0).machine.terminalMemory := by decide +kernel
  obtain ⟨cell, _, code, last⟩ := final _ token
  change cell.addressCode = (Cell.register 12).addressCode at code
  have same := Trace.Proofs.cell_address_injective code
  subst cell
  have value : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus).word.toBitVec = 1 := by decide +kernel
  exact ⟨start, finish, after, newer, by simpa only [old] using read,
    by simpa only [result] using written, future, by simpa only [value] using last⟩

theorem copy_then_native_addi : ∃ middle after : State,
    (Cell.register 12).read middle = .ok 0 middle ∧
    run (normalStep (SailRV32.Functions.execute_ITYPE 1 (.Regidx 12) (.Regidx 12) .ADDI))
      (Trace.Proofs.retiredState middle 4) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.Proofs.retiredState after 8) ∧
    (Cell.register 12).read after = .ok 1 after := by
  obtain ⟨events, after, permutation, order, history, _, _, final⟩ := shared_machine_worker_effects.execution
  have bounds : ∀ event ∈ (mixedData 0).mixedSteps.map transferEvent, 4 < event.1 ∧ event.1 ≤ 12 := by decide +kernel
  have actual : ∀ event ∈ events, 4 < event.1 ∧ event.1 ≤ 12 :=
    fun event member => bounds event (permutation.mem_iff.mp member)
  obtain ⟨start, middle, _, past, call, future⟩ := Trace.Proofs.history_window order history (by omega : 4 ≤ 8)
  have empty : (events.filter fun event => decide (event.1 ≤ 4)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member less
    exact Nat.not_le.mpr (actual event member).1 (of_decide_eq_true less)
  rw [empty] at past
  cases past
  have callerMember : sharedCaller ∈ (mixedData 0).machine.rows := List.mem_cons_of_mem _ List.mem_cons_self
  have called : sharedCaller ∈ (mixedData 0).callers := List.mem_singleton_self _
  have callerLow : Delegation.Caller.startClock sharedCaller = 4 := by decide +kernel
  have callerHigh : Delegation.Caller.finishClock sharedCaller = 8 := by decide +kernel
  have callPerm := UnifiedReduced.Caller.Proofs.cycle_window_permutation (by decide) (by decide)
    mixedChecks mixedInputs.publicProgram shared_machine_worker_effects.requests permutation callerMember (by decide +kernel)
  rw [callerLow, callerHigh] at callPerm
  obtain ⟨native, included, _, nativePerm, nativeHistory⟩ :=
    UnifiedReduced.Caller.Proofs.caller_cycle_worker_history shared_machine_worker_effects.requests called callPerm call
  have same : native = worker := List.mem_singleton.mp included
  subst native
  have distinct : ((worker.memorySteps.map transferEvent).map fun event => event.2.1).Nodup := by decide +kernel
  have currentDistinct := (nativePerm.map (fun event => event.2.1)).nodup_iff.mpr distinct
  have readable : ∀ cell ∈ cells, ∃ value, cell.read mixedBefore = .ok value mixedBefore := by
    intro cell member
    obtain ⟨_, _, value, read, _⟩ := Trace.Proofs.image_cell_source mixedInputs.initialization cell member
    exact ⟨value, read⟩
  have nonzero : ∀ event ∈ (events.filter fun event => decide (4 < event.1 ∧ event.1 ≤ 8)).filter
      (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)), event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have observations := Delegation.Proofs.atomic_observations nativeHistory mixedInputs.aligned nonzero readable currentDistinct
  let control := Bigint.importedConstraintsMemoryPorts[18]
  have controlMember : transferEvent (readToken worker.assignment control, worker.writeToken control) ∈
      worker.memorySteps.map transferEvent := List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨control, by decide +kernel, rfl⟩, rfl⟩
  obtain ⟨cell, _, address, _, written⟩ := observations _ (nativePerm.mem_iff.mpr controlMember)
  have addressCode : (transferEvent (readToken worker.assignment control, worker.writeToken control)).2.1 =
      (Cell.register 12).addressCode := by decide +kernel
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective (address.trans addressCode)
  subst cell
  have zero : Trace.Proofs.memoryWord (transferEvent (readToken worker.assignment control, worker.writeToken control)).2.2.2 = 0 := by decide +kernel
  have middleRead : (Cell.register 12).read middle = .ok 0 middle := by simpa only [zero] using written
  have ordinaryMember : ordinary 0 ∈ (mixedData 0).machine.rows := List.mem_cons_self
  have notCalled : ordinary 0 ∉ (mixedData 0).callers := by
    intro member
    have chosen := of_decide_eq_true (List.mem_filter.mp member).2
    have disabled : ¬ UnifiedReduced.Caller.Selected (ordinary 0).assignment := by decide +kernel
    exact disabled chosen
  have low : Delegation.Caller.startClock (ordinary 0) = 8 := by decide +kernel
  have high : Delegation.Caller.finishClock (ordinary 0) = 12 := by decide +kernel
  have ordinaryPerm := UnifiedReduced.Caller.Proofs.cycle_window_permutation (by decide) (by decide)
    mixedChecks mixedInputs.publicProgram shared_machine_worker_effects.requests permutation ordinaryMember (by decide +kernel)
  rw [low, high] at ordinaryPerm
  have sameFuture : (events.filter fun event => decide (8 < event.1 ∧ event.1 ≤ 12)) =
      (events.filter fun event => decide (8 < event.1)) := by
    apply List.filter_congr
    intro event member
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact and_iff_left (actual event member).2
  rw [sameFuture] at ordinaryPerm
  have current : Trace.Proofs.SailHistory cells (Trace.Proofs.rowEvents 1 (ordinary 0)).reverse middle after :=
    UnifiedReduced.Caller.Proofs.ordinary_cycle_history (by decide) (by decide) mixedChecks mixedInputs.publicProgram
      ordinaryMember notCalled ordinaryPerm (order.sublist List.filter_sublist) future
  let input : Input := ⟨⟨.addi, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨4, 0⟩⟩,
    .Regidx 12, .Regidx 0, .Regidx 12, 1, 0, Trace.Proofs.retiredState middle 4⟩
  have contract : Contract input := by
    constructor
    · intro _
      exact ⟨0, Trace.Proofs.cell_read_PC _ (Trace.Proofs.cell_read_nextPC _ middleRead 4) 4, by intro _; rfl⟩
    · intro impossible
      simp only [input] at impossible
      cases impossible <;> contradiction
    · intro _ _
      dsimp only [input]
      decide +kernel
    · intro _ impossible
      simp only [input] at impossible
      cases impossible <;> contradiction
    · exact Trace.Proofs.retired_state_pc middle 4
  have spec := step_of_destination (output := ⟨⟨1, 0⟩, ⟨8, 0⟩⟩) contract (by dsimp only [input]; decide +kernel) (by
    intro state admissible
    exact spec_of_result admissible (by dsimp only [input]; decide +kernel)
      (by dsimp only [input]; decide +kernel))
  have fields : UnifiedReduced.decoderFields mixedProgram[0].instruction = some mixedProgram[0].data := by with_unfolding_all rfl
  have query : UnifiedReduced.decoderQuery (arithmetic 0) = mixedProgram[0].query := by decide +kernel
  have nativeStep := UnifiedReduced.Proofs.register_retirement (by decide) (arithmeticCore 0) fields query
    (by decide +kernel) (by decide +kernel : mixedProgram[0].data.rd = (12 : BitVec 5)) 1 current spec
  have token : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus) ∈
      (mixedData 0).machine.terminalMemory := by decide +kernel
  obtain ⟨cell, _, address, read⟩ := final _ token
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have value : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus).word.toBitVec = 1 := by decide +kernel
  exact ⟨middle, after, middleRead, nativeStep, by simpa only [value] using read⟩

theorem fabricated_read_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic 1)) (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.table mixedBefore)) :=
  Verification.holds_append (arithmeticCore 1) (arithmeticTimestamps 1)

theorem fabricated_read_breaks_joint_matching : ¬ UnifiedReduced.Caller.MixedMemoryAccepted (mixedData 1) mixedProgram := by
  intro bad
  have missing : ¬ ((mixedData 1).machine.initialMemory ++ (mixedData 1).mixedSteps.map Prod.snd).Perm
      ((mixedData 1).machine.terminalMemory ++ (mixedData 1).mixedSteps.map Prod.fst) := by decide +kernel
  exact missing bad.memory

end Tests.UnifiedDelegation
