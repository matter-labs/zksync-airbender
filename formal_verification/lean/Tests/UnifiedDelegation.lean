import Airbender.Review.Trace.UnifiedReduced.Theorems
import Tests.DelegationCaller
import Tests.BigintMemory
import Tests.DelegationOperationEffects
import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup

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

theorem issued_copy_window :
    Delegation.Caller.RequestWindowBinding requests.callers requests.workers 4 8 :=
  UnifiedReduced.Caller.request_window_soundness (by decide +kernel) (by decide +kernel)
    requestChecks requestInputs (by decide) (by decide) (by decide)

theorem issued_copy_window_count :
    (Delegation.Caller.windowCallers requests.callers 4 8).length = 1 :=
  (Delegation.Caller.Proofs.window_call_count issued_copy_window).trans (by decide +kernel)

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

theorem joint_copy_window :
    UnifiedReduced.Caller.MixedWindowExecution (mixedData 0) mixedBefore cells 4 8 :=
  UnifiedReduced.Caller.mixed_window_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    mixedAccepted mixedInputs (by decide) (by decide) (by decide) (by decide)

theorem joint_preparation_window :
    UnifiedReduced.Caller.MixedWindowExecution (mixedData 0) mixedBefore cells 8 12 :=
  UnifiedReduced.Caller.mixed_window_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    mixedAccepted mixedInputs (by decide) (by decide) (by decide) (by decide)

theorem mixed_instruction_window_counts :
    ((mixedData 0).windowMachineRows 4 12).length = (12 - 4) / 4 ∧
      ((mixedData 0).windowMachineRows 8 12).length = (12 - 8) / 4 := by
  constructor
  all_goals
    exact UnifiedReduced.Caller.Proofs.machine_window_count (by decide +kernel) (by decide +kernel)
      mixedChecks mixedInputs.publicProgram (by decide) (by decide) (by decide) (by decide) (by decide)

theorem derived_copy_region : UnifiedReduced.Caller.CallerWindowSchedule (mixedData 0) 4 8 :=
  UnifiedReduced.Caller.window_schedule_soundness (by decide +kernel) (by decide +kernel)
    mixedChecks mixedInputs.publicProgram (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel)

theorem ordinary_region_rejected : ¬ UnifiedReduced.Caller.CallerWindowSchedule (mixedData 0) 8 12 := by
  intro schedule
  have rows := schedule.rows
  change [] = [ordinary 0] at rows
  contradiction

theorem ordinary_region_duration_rejected :
    ¬ 12 = 8 + 4 * ((mixedData 0).workers.windowRows 8 12).length := by decide +kernel

theorem mixed_caller_region_projection :
    UnifiedReduced.Caller.MixedProjectedWindowExecution (mixedData 0) mixedBefore cells 4 8 :=
  UnifiedReduced.Caller.mixed_window_projection_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    mixedAccepted mixedInputs (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel)

theorem empty_region_after_preparation :
    UnifiedReduced.Caller.MixedProjectedWindowExecution (mixedData 0) mixedBefore cells 12 12 :=
  UnifiedReduced.Caller.mixed_window_projection_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    mixedAccepted mixedInputs (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel)

private theorem boundary_control {tokens : List (MemoryToken babyBearModulus)} {state : State}
    (image : UnifiedReduced.Caller.NativeBoundary tokens state cells)
    {clock value : Nat} (member : (⟨(Cell.register 12).addressCode, (clock, 0), Nat.pair value 0⟩ :
      MemoryToken babyBearModulus) ∈ tokens) :
    (Cell.register 12).read state = .ok (Word.mk value 0).toBitVec state := by
  obtain ⟨cell, _, address, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read image member
  change cell.addressCode = (Cell.register 12).addressCode at address
  have equal := Trace.Proofs.cell_address_injective address
  subst cell
  simpa only [MemoryToken.word, Nat.unpair_pair] using read

private theorem endpoint_permutation {start finish target : List (MemoryToken babyBearModulus)}
    {steps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    (matching : (start ++ steps.map Prod.snd).Perm (finish ++ steps.map Prod.fst))
    (expected : (start ++ steps.map Prod.snd).Perm (target ++ steps.map Prod.fst)) : finish.Perm target :=
  (List.perm_append_right_iff _).mp (matching.symm.trans expected)

theorem mixed_projected_prefix_control : ∃ tokens events state,
    events.Perm (((mixedData 0).prefixSteps 12).map transferEvent) ∧
    Trace.SailHistory cells events mixedBefore state ∧
    UnifiedReduced.Caller.NativeBoundary tokens state cells ∧
    (Cell.register 12).read state = .ok 1 state ∧
    (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus) ∈ tokens := by
  obtain ⟨start, finish, earlier, current, atStart, atFinish, earlierPerm, _,
    earlierHistory, _, prefixMatching, _, startBoundary, _⟩ := empty_region_after_preparation.execution
  have allSteps : (mixedData 0).prefixSteps 12 = (mixedData 0).mixedSteps := by decide +kernel
  rw [allSteps] at prefixMatching
  have actual : start.Perm (mixedData 0).machine.terminalMemory :=
    (List.perm_append_right_iff _).mp (prefixMatching.symm.trans mixedAccepted.memory)
  have present : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus) ∈ start :=
    actual.mem_iff.mpr (by decide +kernel)
  refine ⟨start, earlier, atStart, earlierPerm, earlierHistory, startBoundary, ?_, present⟩
  have word : (Word.mk 1 0).toBitVec = (1 : BitVec 32) := by decide +kernel
  simpa only [word] using boundary_control startBoundary present

theorem joint_copy_controls : ∃ earlier current start finish,
    earlier.Perm (((mixedData 0).prefixSteps 4).map transferEvent) ∧
    current.Perm (((mixedData 0).windowSteps 4 8).map transferEvent) ∧
    Trace.SailHistory cells earlier mixedBefore start ∧ Trace.SailHistory cells current start finish ∧
    (Cell.register 12).read start = .ok 128 start ∧ (Cell.register 12).read finish = .ok 0 finish ∧
    ∃ tokens, UnifiedReduced.Caller.NativeBoundary tokens finish cells ∧
      (⟨(Cell.register 12).addressCode, (7, 0), 0⟩ : MemoryToken babyBearModulus) ∈ tokens := by
  obtain ⟨seeds, finalTokens, earlier, current, start, finish, earlierPerm, currentPerm,
    earlierHistory, currentHistory, prefixMatching, matching, seedImage, finalImage⟩ := joint_copy_window.execution
  have empty : (mixedData 0).prefixSteps 4 = [] := by decide +kernel
  have initial : seeds.Perm (mixedData 0).machine.initialMemory := by
    simpa only [empty, List.map_nil, List.append_nil] using prefixMatching.symm
  have actual := (initial.symm.append_right _).trans matching
  have expected : ((mixedData 0).machine.initialMemory ++
      ((mixedData 0).windowSteps 4 8).map Prod.snd).Perm
      (base.machine.terminalMemory ++ ((mixedData 0).windowSteps 4 8).map Prod.fst) := by decide +kernel
  have finalPerm := endpoint_permutation actual expected
  have initialMember : (⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 128 0⟩ : MemoryToken babyBearModulus) ∈
      seeds := initial.mem_iff.mpr (by decide +kernel)
  have finalMember : (⟨(Cell.register 12).addressCode, (7, 0), 0⟩ : MemoryToken babyBearModulus) ∈
      finalTokens := finalPerm.mem_iff.mpr (by decide +kernel)
  exact ⟨earlier, current, start, finish, earlierPerm, currentPerm, earlierHistory, currentHistory,
    boundary_control seedImage initialMember, boundary_control finalImage finalMember,
    finalTokens, finalImage, finalMember⟩

theorem joint_preparation_controls : ∃ earlier current start finish,
    earlier.Perm (((mixedData 0).prefixSteps 8).map transferEvent) ∧
    current.Perm (((mixedData 0).windowSteps 8 12).map transferEvent) ∧
    Trace.SailHistory cells earlier mixedBefore start ∧ Trace.SailHistory cells current start finish ∧
    (Cell.register 12).read start = .ok 0 start ∧ (Cell.register 12).read finish = .ok 1 finish ∧
    ∃ tokens, UnifiedReduced.Caller.NativeBoundary tokens start cells ∧
      (⟨(Cell.register 12).addressCode, (7, 0), 0⟩ : MemoryToken babyBearModulus) ∈ tokens := by
  obtain ⟨seeds, finalTokens, earlier, current, start, finish, earlierPerm, currentPerm,
    earlierHistory, currentHistory, prefixMatching, matching, seedImage, finalImage⟩ := joint_preparation_window.execution
  have expected : ((mixedData 0).machine.initialMemory ++ ((mixedData 0).prefixSteps 8).map Prod.snd).Perm
      (base.machine.terminalMemory ++ ((mixedData 0).prefixSteps 8).map Prod.fst) := by decide +kernel
  have initial := endpoint_permutation prefixMatching expected
  have actual := (initial.symm.append_right _).trans matching
  have expectedFinal : (base.machine.terminalMemory ++ ((mixedData 0).windowSteps 8 12).map Prod.snd).Perm
      ((mixedData 0).machine.terminalMemory ++ ((mixedData 0).windowSteps 8 12).map Prod.fst) := by decide +kernel
  have finalPerm := endpoint_permutation actual expectedFinal
  have initialMember : (⟨(Cell.register 12).addressCode, (7, 0), 0⟩ : MemoryToken babyBearModulus) ∈
      seeds := initial.mem_iff.mpr (by decide +kernel)
  have finalMember : (⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 1 0⟩ : MemoryToken babyBearModulus) ∈
      finalTokens := finalPerm.mem_iff.mpr (by decide +kernel)
  exact ⟨earlier, current, start, finish, earlierPerm, currentPerm, earlierHistory, currentHistory,
    boundary_control seedImage initialMember, boundary_control finalImage finalMember,
    seeds, seedImage, initialMember⟩

private def callerOnlyData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [sharedCaller]
    rom := UnifiedReduced.Setup.table mixedBefore
    initial := sharedCaller.start
    terminal := sharedCaller.finish
    initialMemory := base.machine.initialMemory
    terminalMemory := base.machine.terminalMemory }
  workers := { base.workers with initial := [], terminal := [] }
  program := [Tests.DelegationCaller.entry .bigint]

private theorem callerOnlyAccepted : UnifiedReduced.Caller.MixedMemoryAccepted callerOnlyData [] := by
  refine ⟨⟨?_, ?_, List.Perm.swap _ _ [], ?_, mixedChecks.workerConstraints,
    mixedChecks.workerActive, mixedChecks.requests⟩, ?_, ?_⟩
  · intro row member
    have same : row = sharedCaller := List.mem_singleton.mp member
    subst row
    exact mixedChecks.constraints sharedCaller (by simp [mixedData])
  · intro row member
    have same : row = sharedCaller := List.mem_singleton.mp member
    subst row
    exact mixedChecks.active sharedCaller (by simp [mixedData])
  · intro row member
    exact mixedChecks.decoded row member
  · intro row member ordinaryRow
    have same : row = sharedCaller := List.mem_singleton.mp member
    subst row
    have caller : sharedCaller ∈ callerOnlyData.callers := by
      change sharedCaller ∈ [sharedCaller]
      exact List.mem_singleton_self _
    exact False.elim (ordinaryRow caller)
  · decide +kernel

private theorem callerOnlyInputs :
    UnifiedReduced.Caller.MixedMemoryInputs callerOnlyData [] mixedBefore [0] [] cells :=
  ⟨⟨mixedInputs.publicProgram.image, mixedInputs.publicProgram.initialClock, mixedInputs.publicProgram.initialAligned⟩,
    rfl, mixedInitialization, mixedInputs.distinct, mixedInputs.aligned,
    rfl, mixedInputs.tables, mixedInputs.rounds⟩

theorem worker_window_ignores_supplied_boundaries :
    UnifiedReduced.Caller.ProjectedWindowExecution callerOnlyData mixedBefore cells 4 8 :=
  UnifiedReduced.Caller.window_projection_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    callerOnlyAccepted callerOnlyInputs (by decide) (by decide) (by decide) (by decide)

theorem projected_window_native_control : callerOnlyData.workers.initial = [] ∧ callerOnlyData.workers.terminal = [] ∧
    ∃ start finish : State, ∃ workerData : Delegation.MemoryData babyBearModulus,
      Delegation.BoundaryMemoryInputs workerData start (Delegation.Caller.workerCells cells) ∧
      Delegation.TraceMapping workerData start finish (Delegation.Caller.workerCells cells) ∧
      (Cell.register 12).read start = .ok 128 start ∧ (Cell.register 12).read finish = .ok 0 finish ∧
      (⟨(Cell.register 12).addressCode, (7, 0), 0⟩ : MemoryToken babyBearModulus) ∈ workerData.terminal := by
  obtain ⟨seeds, terminal, _, _, start, finish, _, _, _, _, _, _, prior, _, selected,
    initialized, _, mapping⟩ := worker_window_ignores_supplied_boundaries.execution
  have empty : (callerOnlyData.prefixProjection 4 seeds).steps = [] := by
    change ((callerOnlyData.workers.prefixRows 4).flatMap Delegation.Row.memorySteps) = []
    decide +kernel
  have initial : callerOnlyData.workerProjection.initial.Perm
      (callerOnlyData.windowProjection 4 8 seeds terminal).initial := by
    have fresh := prior.matching
    simp only [empty, List.map_nil, List.append_nil] at fresh
    exact fresh
  have actual := (initial.append_right _).trans selected.matching
  have expected : (callerOnlyData.workerProjection.initial ++
      (callerOnlyData.windowProjection 4 8 seeds terminal).steps.map Prod.snd).Perm
      (callerOnlyData.workerProjection.terminal ++
        (callerOnlyData.windowProjection 4 8 seeds terminal).steps.map Prod.fst) := by
    change (callerOnlyData.workerProjection.initial ++
      ((callerOnlyData.workers.windowRows 4 8).flatMap Delegation.Row.memorySteps).map Prod.snd).Perm
      (callerOnlyData.workerProjection.terminal ++
        ((callerOnlyData.workers.windowRows 4 8).flatMap Delegation.Row.memorySteps).map Prod.fst)
    decide +kernel
  have finalPerm := endpoint_permutation actual expected
  have firstToken : (⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 128 0⟩ : MemoryToken babyBearModulus) ∈
      (callerOnlyData.windowProjection 4 8 seeds terminal).initial := initial.mem_iff.mp (by decide +kernel)
  have lastToken : (⟨(Cell.register 12).addressCode, (7, 0), 0⟩ : MemoryToken babyBearModulus) ∈
      (callerOnlyData.windowProjection 4 8 seeds terminal).terminal := finalPerm.mem_iff.mpr (by decide +kernel)
  obtain ⟨firstCell, _, firstCode, firstRead⟩ := initialized.toBoundaryInputs.reads _ firstToken
  obtain ⟨lastCell, _, lastCode, lastRead⟩ := mapping.finalCells _ lastToken
  change firstCell.addressCode = (Cell.register 12).addressCode at firstCode
  change lastCell.addressCode = (Cell.register 12).addressCode at lastCode
  have firstEq := Trace.Proofs.cell_address_injective firstCode
  have lastEq := Trace.Proofs.cell_address_injective lastCode
  subst firstCell
  subst lastCell
  refine ⟨rfl, rfl, start, finish, _, initialized, mapping, ?_, lastRead, lastToken⟩
  have value : (Word.mk 128 0).toBitVec = (128 : BitVec 32) := by decide +kernel
  simpa only [memoryWord, Nat.unpair_pair, value] using firstRead

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
    Trace.SailHistory cells newer finish after ∧
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

private def arithmeticView : Input :=
  ⟨⟨.addi, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨4, 0⟩⟩,
    .Regidx 12, .Regidx 0, .Regidx 12, 1, 0, mixedBefore⟩

theorem shared_arithmetic_cycle : ∃ events finalState,
    events.Perm ((mixedData 0).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events mixedBefore finalState ∧
    UnifiedReduced.Caller.RetiresCycle cells events mixedBefore finalState (ordinary 0)
      (SailRV32.Functions.execute_ITYPE 1 (.Regidx 12) (.Regidx 12) .ADDI) := by
  apply UnifiedReduced.Caller.arithmetic_cycle_soundness mixedAccepted mixedInputs (by decide +kernel)
    (input := arithmeticView) (List.mem_cons_self)
  · constructor <;> dsimp only [arithmeticView] <;> decide +kernel
  · intro index source
    simp only [arithmeticView, SailRV32.regidx.Regidx.injEq] at source
    rcases source with rfl | rfl
    all_goals decide +kernel
  · refine ⟨mixedProgram[0], List.mem_cons_self, ?_, ?_⟩
    · decide +kernel
    · rfl

theorem copy_then_native_addi : ∃ middle after : State,
    (Cell.register 12).read middle = .ok 0 middle ∧
    run (normalStep (SailRV32.Functions.execute_ITYPE 1 (.Regidx 12) (.Regidx 12) .ADDI))
      (Trace.retiredState middle 4) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.retiredState after 8) ∧
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
  have zero : Trace.memoryWord (transferEvent (readToken worker.assignment control, worker.writeToken control)).2.2.2 = 0 := by decide +kernel
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
  have current : Trace.SailHistory cells (Trace.rowEvents 1 (ordinary 0)).reverse middle after :=
    UnifiedReduced.Caller.Proofs.ordinary_cycle_history (by decide) (by decide) mixedChecks mixedInputs.publicProgram
      ordinaryMember notCalled ordinaryPerm (order.sublist List.filter_sublist) future
  let input : Input := ⟨⟨.addi, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨4, 0⟩⟩,
    .Regidx 12, .Regidx 0, .Regidx 12, 1, 0, Trace.retiredState middle 4⟩
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

private def customBits (kind : Fin 5) : BitVec 32 :=
  #[0xc2004673, 0xc1c04673, 0x8dc04673, 0x89c04673, 0x85f04673][kind.val]!
private def customBefore (kind : Fin 5) : State :=
  wordWriteState Tests.DelegationOperationEffects.before 4 (customBits kind)
private def customEntry (kind : Fin 5) : UnifiedReduced.ProgramEntry :=
  ⟨4, customBits kind,
    if kind.val = 0 then .ZIMOP_MOP_RR (4, .Regidx 0, .Regidx 0, .Regidx 12)
    else .ZIMOP_MOP_R (#[16, 12, 8, 7][kind.val - 1]!, .Regidx 0, .Regidx 12),
    ⟨.machine, 0, if kind.val = 0 then 0 else 12, 12, ⟨0, 0⟩,
      if kind.val = 0 then 512 else 65536, if kind.val = 0 then 0 else 46 + kind.val⟩⟩
private def customAssignment (kind : Fin 5) (column : Nat) : ZMod babyBearModulus :=
  if 92 ≤ column ∧ column < 128 ∧ (column - 92) % 9 = 0 ∧ kind.val ≠ 0 then (46 + kind.val : Nat)
  else match column with
    | 0 => 4
    | 2 | 30 => 8
    | 32 | 7 | 44 => 12
    | 4 | 129 | 130 | 131 | 132 | 133 => 1
    | 6 | 38 => if kind.val = 0 then 0 else 12
    | 10 => if kind.val = 0 then 0 else (46 + kind.val : Nat)
    | 20 => if kind.val = 0 then 1 else 0
    | 27 => if kind.val = 0 then 0 else 1
    | 34 => 6
    | 40 => if kind.val = 0 then 8 else 7
    | 46 => if kind.val = 0 then 7 else 9
    | 88 => if kind.val = 0 then 0 else 3
    | _ => 0
private def customRow (kind : Fin 5) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, customAssignment kind⟩
private def customTerminal (kind : Fin 5) : List (MemoryToken babyBearModulus) :=
  base.machine.terminalMemory.map fun token =>
    if token.address = (Cell.register 0).addressCode then
      ⟨token.address, (if kind.val = 0 then 9 else 8, 0), 0⟩
    else if token.address = (Cell.register 12).addressCode then ⟨token.address, (10, 0), 0⟩
    else token
private def customData (kind : Fin 5) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [customRow kind, sharedCaller]
    rom := UnifiedReduced.Setup.table (customBefore kind)
    initial := sharedCaller.start
    terminal := (customRow kind).finish
    initialMemory := base.machine.initialMemory
    terminalMemory := customTerminal kind }
  workers := base.workers
  program := [Tests.DelegationCaller.entry .bigint]

private theorem customCore (kind : Fin 5) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (customAssignment kind))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (customBefore kind))) := by
  fin_cases kind
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, customAssignment, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨⟨0, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)
    | (refine ⟨⟨1, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)
    | (refine ⟨⟨786817, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)
    | (refine ⟨⟨852353, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)
    | (refine ⟨⟨917889, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)
    | (refine ⟨⟨983425, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)

private theorem customClocks (kind : Fin 5) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (customAssignment kind)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases kind <;> decide +kernel

private theorem callerCoreFor (state : State) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment sharedAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table state)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, sharedAssignment, assignment, assignmentWith,
    Delegation.Requests.csr, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem customChecks (kind : Fin 5) : UnifiedReduced.Caller.RequestChecks (customData kind) := by
  constructor
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact Verification.holds_append (customCore kind) (customClocks kind)
    · have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (callerCoreFor (customBefore kind)) sharedTimestamps
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · fin_cases kind <;> decide +kernel
    · have same := List.mem_singleton.mp member
      subst row
      decide +kernel
  · change ([sharedCaller.start] ++ [(customRow kind).finish, sharedCaller.finish]).Perm
      ([(customRow kind).finish, sharedCaller.finish] ++ [sharedCaller.start])
    exact List.perm_append_comm
  · intro row member
    have same : row = sharedCaller := by
      have callers : (customData kind).callers = [sharedCaller] := by fin_cases kind <;> rfl
      rw [callers] at member
      exact List.mem_singleton.mp member
    subst row
    change ∃ i : Fin 1, UnifiedReduced.decoderQuery sharedAssignment =
      Delegation.Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
    exact ⟨0, by decide +kernel⟩
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerConstraints
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerActive
  · exact Tests.DelegationOperationEffects.sharedAccepted.requests

private theorem customAccepted (kind : Fin 5) :
    UnifiedReduced.Caller.MixedMemoryAccepted (customData kind) [customEntry kind] := by
  refine ⟨customChecks kind, ?_, ?_⟩
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · change ∃ i : Fin 1, (customRow kind).decoderQuery = ([customEntry kind].get i).query
      exact ⟨0, by fin_cases kind <;> decide +kernel⟩
    · have same := List.mem_singleton.mp member
      subst row
      exact False.elim (noncaller (by
        fin_cases kind <;> exact List.mem_singleton_self _))
  · fin_cases kind <;> decide +kernel

private theorem initializedAfterCode (bits : BitVec 32) :
    initialImage (wordWriteState Tests.DelegationOperationEffects.before 4 bits) cells = some base.machine.initialMemory := by
  apply Trace.Proofs.image_frame Tests.DelegationOperationEffects.sharedInputs.initialization
  intro cell member value read
  cases cell with
  | register index =>
    exact rX_register_frame (by dsimp only [wordWriteState]) index read
  | ram address =>
    have lower : 8 ≤ address.toNat := by
      simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
      rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
      all_goals interval_cases i <;> decide
    exact written_word_disjoint 4 _ (Or.inr lower) read

private theorem customInitialization (kind : Fin 5) :
    initialImage (customBefore kind) cells = some (customData kind).machine.initialMemory := initializedAfterCode (customBits kind)

private theorem customInputs (kind : Fin 5) : UnifiedReduced.Caller.MixedMemoryInputs
    (customData kind) [customEntry kind] (customBefore kind) [0] [4] cells := by
  refine ⟨?_, ?_, customInitialization kind, Tests.DelegationOperationEffects.sharedInputs.distinct,
    Tests.DelegationOperationEffects.sharedInputs.aligned, rfl,
    Tests.DelegationOperationEffects.sharedInputs.tables, Tests.DelegationOperationEffects.sharedInputs.rounds⟩
  · constructor
    · have bytes : (Cell.ram 0).read (customBefore kind) =
          .ok (Tests.DelegationCaller.entry .bigint).bits (customBefore kind) :=
        written_word_disjoint 4 _ (Or.inl (by decide)) (written_word_read Tests.BigintMemory.before 0 _)
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits)
          (customBefore kind) = .ok (Tests.DelegationCaller.entry .bigint).instruction (customBefore kind) :=
        Tests.DelegationCaller.original_decoder .bigint (customBefore kind)
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · change (4 : Nat) % 4 = 0
      decide +kernel
  · have bytes : (Cell.ram 4).read (customBefore kind) = .ok (customBits kind) (customBefore kind) :=
      written_word_read _ _ _
    have decoded : run (SailRV32.Functions.encdec_backwards (customBits kind)) (customBefore kind) =
        .ok (customEntry kind).instruction (customBefore kind) := by
      fin_cases kind <;> with_unfolding_all rfl
    have fields : UnifiedReduced.Mixed.decoderFields (customEntry kind).instruction = some (customEntry kind).data := by
      fin_cases kind <;> with_unfolding_all rfl
    simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl

theorem copy_then_custom_retirement (kind : Fin 5) : ∃ events finalState clause,
    UnifiedReduced.Custom.clauseFor (customEntry kind).instruction = some clause ∧
    events.Perm ((customData kind).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (customBefore kind) finalState ∧
    UnifiedReduced.Caller.RetiresCycle cells events (customBefore kind) finalState (customRow kind) clause := by
  exact UnifiedReduced.Caller.custom_cycle_soundness (customAccepted kind) (customInputs kind)
    (by change (0 : Nat) < 4; decide +kernel) List.mem_cons_self List.mem_cons_self (by fin_cases kind <;> decide +kernel)
    (by fin_cases kind <;> decide +kernel)

private def binaryBefore : State := wordWriteState Tests.DelegationOperationEffects.before 4 0x00164613
private def binaryEntry : UnifiedReduced.ProgramEntry :=
  ⟨4, 0x00164613, .ITYPE (1, .Regidx 12, .Regidx 12, .XORI), ⟨.machine, 12, 0, 12, ⟨1, 0⟩, 65536, 52⟩⟩
private def binaryAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 10 ∨ column = 92 ∨ column = 101 ∨ column = 110 ∨ column = 119 then 52
  else if column = 27 ∨ column = 58 ∨ column = 94 ∨ column = 95 then 1
  else if column = 88 then 3
  else if column = 11 then 0 else arithmetic 0 column
private def binaryRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, binaryAssignment⟩
private def binaryData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [binaryRow, sharedCaller]
    rom := UnifiedReduced.Setup.table binaryBefore
    initial := sharedCaller.start
    terminal := binaryRow.finish
    initialMemory := base.machine.initialMemory
    terminalMemory := mixedTerminal 0 }
  workers := base.workers
  program := [Tests.DelegationCaller.entry .bigint]

private theorem binaryCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment binaryAssignment) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table binaryBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, binaryAssignment, arithmetic, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | exact ⟨⟨0, by decide⟩, rfl⟩
    | (refine ⟨⟨1, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)
    | (refine ⟨⟨257, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)
    | (refine ⟨⟨258, by decide⟩, ?_⟩; with_unfolding_all decide +kernel)

private theorem binaryClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment binaryAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem binaryChecks : UnifiedReduced.Caller.RequestChecks binaryData := by
  constructor
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact Verification.holds_append binaryCore binaryClocks
    · have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (callerCoreFor binaryBefore) sharedTimestamps
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    · have same := List.mem_singleton.mp member
      subst row
      decide +kernel
  · change ([sharedCaller.start] ++ [binaryRow.finish, sharedCaller.finish]).Perm
      ([binaryRow.finish, sharedCaller.finish] ++ [sharedCaller.start])
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

private theorem binaryAccepted : UnifiedReduced.Caller.MixedMemoryAccepted binaryData [binaryEntry] := by
  refine ⟨binaryChecks, ?_, ?_⟩
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · change ∃ i : Fin 1, binaryRow.decoderQuery = ([binaryEntry].get i).query
      exact ⟨0, by decide +kernel⟩
    · exact False.elim (noncaller member)
  · have same : binaryData.mixedSteps = (mixedData 0).mixedSteps := by decide +kernel
    change (base.machine.initialMemory ++ binaryData.mixedSteps.map Prod.snd).Perm
      (mixedTerminal 0 ++ binaryData.mixedSteps.map Prod.fst)
    rw [same]
    exact mixedAccepted.memory

private theorem binaryInputs : UnifiedReduced.Caller.MixedMemoryInputs binaryData [binaryEntry] binaryBefore [0] [4] cells := by
  refine ⟨?_, ?_, initializedAfterCode 0x00164613, Tests.DelegationOperationEffects.sharedInputs.distinct,
    Tests.DelegationOperationEffects.sharedInputs.aligned, rfl,
    Tests.DelegationOperationEffects.sharedInputs.tables, Tests.DelegationOperationEffects.sharedInputs.rounds⟩
  · constructor
    · have bytes : (Cell.ram 0).read binaryBefore = .ok (Tests.DelegationCaller.entry .bigint).bits binaryBefore :=
        written_word_disjoint 4 _ (Or.inl (by decide)) (written_word_read Tests.BigintMemory.before 0 _)
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) binaryBefore =
          .ok (Tests.DelegationCaller.entry .bigint).instruction binaryBefore :=
        Tests.DelegationCaller.original_decoder .bigint binaryBefore
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · decide +kernel
  · have bytes : (Cell.ram 4).read binaryBefore = .ok 0x00164613 binaryBefore := written_word_read _ _ _
    have decoded : run (SailRV32.Functions.encdec_backwards 0x00164613) binaryBefore = .ok binaryEntry.instruction binaryBefore := by
      with_unfolding_all rfl
    have fields : UnifiedReduced.Mixed.decoderFields binaryEntry.instruction = some binaryEntry.data := by with_unfolding_all rfl
    simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl

private def binaryView : UnifiedReduced.Binary.Input :=
  ⟨.xor, true, 0, 1, ⟨4, 0⟩, .Regidx 12, .Regidx 0, .Regidx 12, 1, binaryBefore⟩

theorem copy_then_xori_retirement : ∃ events finalState,
    events.Perm (binaryData.mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events binaryBefore finalState ∧
    UnifiedReduced.Caller.RetiresCycle cells events binaryBefore finalState binaryRow
      (SailRV32.Functions.execute_ITYPE 1 (.Regidx 12) (.Regidx 12) .XORI) := by
  apply UnifiedReduced.Caller.binary_cycle_soundness binaryAccepted binaryInputs (by decide +kernel) false
    (input := binaryView) List.mem_cons_self
  · constructor <;> decide +kernel
  · exact ⟨binaryEntry, List.mem_cons_self, by decide +kernel, rfl⟩

private def comparisonBefore : State := wordWriteState Tests.DelegationOperationEffects.before 4 0xfff63613
private def comparisonEntry : UnifiedReduced.ProgramEntry :=
  ⟨4, 0xfff63613, .ITYPE (4095, .Regidx 12, .Regidx 12, .SLTIU), ⟨.machine, 12, 0, 12, ⟨65535, 65535⟩, 4096, 3⟩⟩
private def comparisonAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 8 ∨ column = 9 ∨ column = 60 ∨ column = 102 then 65535
  else if column = 10 then 3
  else if column = 11 ∨ column = 57 ∨ column = 90 ∨ column = 129 then 0
  else if column = 23 ∨ column = 52 ∨ column = 53 ∨ column = 59 ∨ column = 61 ∨ column = 78 ∨
      column = 84 ∨ column = 88 ∨ column = 89 ∨ column = 103 ∨ column = 112 then 1
  else if column = 81 ∨ column = 120 ∨ column = 122 then 8
  else if column = 92 ∨ column = 101 then 5
  else if column = 110 then 51
  else if column = 111 then 53
  else if column = 119 then 2
  else arithmetic 0 column
private def comparisonRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, comparisonAssignment⟩
private def comparisonData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [comparisonRow, sharedCaller]
    rom := UnifiedReduced.Setup.table comparisonBefore
    initial := sharedCaller.start
    terminal := comparisonRow.finish
    initialMemory := base.machine.initialMemory
    terminalMemory := mixedTerminal 0 }
  workers := base.workers
  program := [Tests.DelegationCaller.entry .bigint]

private theorem comparisonCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment comparisonAssignment) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table comparisonBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, comparisonAssignment, arithmetic, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨⟨524545, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨524546, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨655617, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨786742, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (refine ⟨⟨786745, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (refine ⟨⟨721152, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨721161, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])

private theorem comparisonClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment comparisonAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem comparisonChecks : UnifiedReduced.Caller.RequestChecks comparisonData := by
  constructor
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact Verification.holds_append comparisonCore comparisonClocks
    · have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (callerCoreFor comparisonBefore) sharedTimestamps
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    · have same := List.mem_singleton.mp member
      subst row
      decide +kernel
  · change ([sharedCaller.start] ++ [comparisonRow.finish, sharedCaller.finish]).Perm
      ([comparisonRow.finish, sharedCaller.finish] ++ [sharedCaller.start])
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

private theorem comparisonAccepted : UnifiedReduced.Caller.MixedMemoryAccepted comparisonData [comparisonEntry] := by
  refine ⟨comparisonChecks, ?_, ?_⟩
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · change ∃ i : Fin 1, comparisonRow.decoderQuery = ([comparisonEntry].get i).query
      exact ⟨0, by decide +kernel⟩
    · exact False.elim (noncaller member)
  · have same : comparisonData.mixedSteps = (mixedData 0).mixedSteps := by decide +kernel
    change (base.machine.initialMemory ++ comparisonData.mixedSteps.map Prod.snd).Perm
      (mixedTerminal 0 ++ comparisonData.mixedSteps.map Prod.fst)
    rw [same]
    exact mixedAccepted.memory

private theorem comparisonInputs : UnifiedReduced.Caller.MixedMemoryInputs comparisonData [comparisonEntry] comparisonBefore [0] [4] cells := by
  refine ⟨?_, ?_, initializedAfterCode 0xfff63613, Tests.DelegationOperationEffects.sharedInputs.distinct,
    Tests.DelegationOperationEffects.sharedInputs.aligned, rfl,
    Tests.DelegationOperationEffects.sharedInputs.tables, Tests.DelegationOperationEffects.sharedInputs.rounds⟩
  · constructor
    · have bytes : (Cell.ram 0).read comparisonBefore = .ok (Tests.DelegationCaller.entry .bigint).bits comparisonBefore :=
        written_word_disjoint 4 _ (Or.inl (by decide)) (written_word_read Tests.BigintMemory.before 0 _)
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) comparisonBefore =
          .ok (Tests.DelegationCaller.entry .bigint).instruction comparisonBefore :=
        Tests.DelegationCaller.original_decoder .bigint comparisonBefore
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · decide +kernel
  · have bytes : (Cell.ram 4).read comparisonBefore = .ok 0xfff63613 comparisonBefore := written_word_read _ _ _
    have decoded : run (SailRV32.Functions.encdec_backwards 0xfff63613) comparisonBefore = .ok comparisonEntry.instruction comparisonBefore := by
      with_unfolding_all rfl
    have fields : UnifiedReduced.Mixed.decoderFields comparisonEntry.instruction = some comparisonEntry.data := by with_unfolding_all rfl
    simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl

private def comparisonView : UnifiedReduced.Control.Comparison.Input :=
  ⟨.sltiu, ⟨0, 0⟩, ⟨65535, 65535⟩, ⟨4, 0⟩, .Regidx 12, .Regidx 0, .Regidx 12, 4095, comparisonBefore⟩

theorem copy_then_sltiu_retirement : ∃ events finalState,
    events.Perm (comparisonData.mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events comparisonBefore finalState ∧
    UnifiedReduced.Caller.RetiresCycle cells events comparisonBefore finalState comparisonRow
      (SailRV32.Functions.execute_ITYPE 4095 (.Regidx 12) (.Regidx 12) .SLTIU) := by
  apply UnifiedReduced.Caller.comparison_cycle_soundness comparisonAccepted comparisonInputs (by decide +kernel)
    (input := comparisonView) List.mem_cons_self
  · constructor <;> decide +kernel
  · exact ⟨comparisonEntry, List.mem_cons_self, by decide +kernel, rfl, by decide +kernel⟩

private def controlBits (kind : Fin 4) : BitVec 32 :=
  (#v[0x00060463, 0x00061463, 0x0080066f, 0x00c60667])[kind]
private def controlBefore (kind : Fin 4) : State :=
  let state := wordWriteState Tests.DelegationOperationEffects.before 4 (controlBits kind)
  {state with regs := ((state.regs.insert .misa (0x40000100 : BitVec 32)).insert
    .cur_privilege .Machine).insert .mseccfg 0}
private def controlEntry (kind : Fin 4) : UnifiedReduced.ProgramEntry :=
  ⟨4, controlBits kind, (#v[.BTYPE (8, .Regidx 0, .Regidx 12, .BEQ),
    .BTYPE (8, .Regidx 0, .Regidx 12, .BNE), .JAL (8, .Regidx 12), .JALR (12, .Regidx 12, .Regidx 12)])[kind],
    ⟨.machine, if kind.val = 2 then 0 else 12, 0, if kind.val < 2 then 0 else 12,
      ⟨if kind.val = 3 then 12 else 8, 0⟩,
      if kind.val < 2 then 24576 else if kind.val = 2 then 1024 else 2048,
      if kind.val = 1 then 1 else 0⟩⟩
private def controlAssignment (kind : Fin 4) (column : Nat) : ZMod babyBearModulus :=
  if column = 5 then (if kind.val = 2 then 0 else 12)
  else if column = 7 ∨ column = 44 then (if kind.val < 2 then 0 else 12)
  else if column = 8 then (if kind.val = 3 then 12 else 8)
  else if column = 10 then (if kind.val = 1 then 1 else 0)
  else if column = 11 ∨ column = 129 then 0
  else if column = 21 then (if kind.val = 2 then 1 else 0)
  else if column = 22 then (if kind.val = 3 then 1 else 0)
  else if column = 24 ∨ column = 25 ∨ column = 57 ∨ column = 85 ∨ column = 90 then (if kind.val < 2 then 1 else 0)
  else if column = 30 ∨ column = 81 ∨ column = 120 ∨ column = 122 then (if kind.val = 1 then 8 else 12)
  else if column = 34 then (if kind.val = 2 then 6 else 7)
  else if column = 40 then (if kind.val = 2 then 8 else 6)
  else if column = 46 then (if kind.val < 2 then 9 else if kind.val = 2 then 7 else 8)
  else if column = 50 ∨ column = 78 ∨ column = 89 then (if kind.val < 2 then 0 else 8)
  else if column = 59 ∨ column = 82 ∨ column = 112 then (if kind.val = 0 then 1 else 0)
  else if column = 83 then (if kind.val < 2 then 0 else 1)
  else if column = 88 then 1
  else if column = 92 ∨ column = 101 then 5
  else if column = 110 then 51
  else if column = 111 then (if kind.val < 2 then if kind.val = 0 then 8 else 24 else 0)
  else if column = 119 then 2
  else arithmetic 0 column
private def controlRow (kind : Fin 4) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, controlAssignment kind⟩
private def controlTerminal (kind : Fin 4) : List (MemoryToken babyBearModulus) :=
  base.machine.terminalMemory.map fun token =>
    if token.address = (Cell.register 0).addressCode then ⟨token.address, (if kind.val < 2 then 10 else 9, 0), 0⟩
    else if token.address = (Cell.register 12).addressCode then
      ⟨token.address, (if kind.val < 2 then 8 else 10, 0), Nat.pair (if kind.val < 2 then 0 else 8) 0⟩
    else token
private def controlData (kind : Fin 4) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [controlRow kind, sharedCaller]
    rom := UnifiedReduced.Setup.table (controlBefore kind)
    initial := sharedCaller.start
    terminal := (controlRow kind).finish
    initialMemory := base.machine.initialMemory
    terminalMemory := controlTerminal kind }
  workers := base.workers
  program := [Tests.DelegationCaller.entry .bigint]

private theorem controlCore (kind : Fin 4) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (controlAssignment kind)) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (controlBefore kind))) := by
  fin_cases kind
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, controlAssignment, arithmetic, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨⟨524545, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨524553, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨655617, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨786689, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (refine ⟨⟨786697, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (refine ⟨⟨786713, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (refine ⟨⟨721161, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨721165, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])

private theorem controlClocks (kind : Fin 4) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (controlAssignment kind)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases kind <;> decide +kernel

private theorem controlChecks (kind : Fin 4) : UnifiedReduced.Caller.RequestChecks (controlData kind) := by
  constructor
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact Verification.holds_append (controlCore kind) (controlClocks kind)
    · have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (callerCoreFor (controlBefore kind)) sharedTimestamps
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · fin_cases kind <;> decide +kernel
    · have same := List.mem_singleton.mp member
      subst row
      decide +kernel
  · change ([sharedCaller.start] ++ [(controlRow kind).finish, sharedCaller.finish]).Perm
      ([(controlRow kind).finish, sharedCaller.finish] ++ [sharedCaller.start])
    exact List.perm_append_comm
  · intro row member
    have same : row = sharedCaller := by
      have callers : (controlData kind).callers = [sharedCaller] := by fin_cases kind <;> rfl
      rw [callers] at member
      exact List.mem_singleton.mp member
    subst row
    change ∃ i : Fin 1, UnifiedReduced.decoderQuery sharedAssignment =
      Delegation.Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
    exact ⟨0, by decide +kernel⟩
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerConstraints
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerActive
  · exact Tests.DelegationOperationEffects.sharedAccepted.requests

private theorem controlAccepted (kind : Fin 4) : UnifiedReduced.Caller.MixedMemoryAccepted (controlData kind) [controlEntry kind] := by
  refine ⟨controlChecks kind, ?_, ?_⟩
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · change ∃ i : Fin 1, (controlRow kind).decoderQuery = ([controlEntry kind].get i).query
      exact ⟨0, by fin_cases kind <;> decide +kernel⟩
    · have same := List.mem_singleton.mp member
      subst row
      exact False.elim (noncaller (by fin_cases kind <;> exact List.mem_singleton_self _))
  · fin_cases kind <;> decide +kernel

private theorem controlInitialization (kind : Fin 4) :
    initialImage (controlBefore kind) cells = some base.machine.initialMemory := by
  apply Trace.Proofs.image_frame (initializedAfterCode (controlBits kind))
  intro cell member value read
  cases cell with
  | ram address =>
    exact read_word_frame
      (before := wordWriteState Tests.DelegationOperationEffects.before 4 (controlBits kind))
      (after := controlBefore kind) rfl read
  | register index =>
    simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first
      | (change EStateM.Result.ok (0 : BitVec 32) _ = .ok value _ at read
         rw [← (EStateM.Result.ok.inj read).1]; rfl)
      | (change run (SailRV32.readReg .x10) _ = .ok value _ at read ⊢
         apply read_register
         simpa [controlBefore, Std.ExtDHashMap.get?_insert] using read_register_iff.mp read)
      | (change run (SailRV32.readReg .x11) _ = .ok value _ at read ⊢
         apply read_register
         simpa [controlBefore, Std.ExtDHashMap.get?_insert] using read_register_iff.mp read)
      | (change run (SailRV32.readReg .x12) _ = .ok value _ at read ⊢
         apply read_register
         simpa [controlBefore, Std.ExtDHashMap.get?_insert] using read_register_iff.mp read)

private theorem controlInputs (kind : Fin 4) : UnifiedReduced.Caller.MixedMemoryInputs (controlData kind) [(controlEntry kind)] (controlBefore kind) [0] [4] cells := by
  refine ⟨?_, ?_, controlInitialization kind, Tests.DelegationOperationEffects.sharedInputs.distinct,
    Tests.DelegationOperationEffects.sharedInputs.aligned, rfl,
    Tests.DelegationOperationEffects.sharedInputs.tables, Tests.DelegationOperationEffects.sharedInputs.rounds⟩
  · constructor
    · have bytes : (Cell.ram 0).read (controlBefore kind) = .ok (Tests.DelegationCaller.entry .bigint).bits (controlBefore kind) :=
        read_word_frame (before := wordWriteState Tests.DelegationOperationEffects.before 4 (controlBits kind))
          (after := controlBefore kind) rfl (written_word_disjoint 4 _ (Or.inl (by decide)) (written_word_read Tests.BigintMemory.before 0 _))
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) (controlBefore kind) =
          .ok (Tests.DelegationCaller.entry .bigint).instruction (controlBefore kind) :=
        Tests.DelegationCaller.original_decoder .bigint (controlBefore kind)
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · change (4 : Nat) % 4 = 0; decide
  · have bytes : (Cell.ram 4).read (controlBefore kind) = .ok (controlBits kind) (controlBefore kind) := read_word_frame (before := wordWriteState Tests.DelegationOperationEffects.before 4 (controlBits kind))
          (after := controlBefore kind) rfl (written_word_read _ _ _)
    have decoded : run (SailRV32.Functions.encdec_backwards (controlBits kind)) (controlBefore kind) = .ok (controlEntry kind).instruction (controlBefore kind) := by
      fin_cases kind <;> with_unfolding_all rfl
    have fields : UnifiedReduced.Mixed.decoderFields (controlEntry kind).instruction = some (controlEntry kind).data := by fin_cases kind <;> with_unfolding_all rfl
    simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl

private def branchView (taken : Bool) : UnifiedReduced.Control.Branch.Input :=
  ⟨if taken then .BEQ else .BNE, ⟨0, 0⟩, ⟨0, 0⟩, ⟨8, 0⟩, ⟨4, 0⟩,
    .Regidx 12, .Regidx 0, 8, default⟩
private def branchKind (taken : Bool) : Fin 4 := if taken then 0 else 1
private def jumpView (indirect : Bool) : UnifiedReduced.Jump.Input :=
  ⟨if indirect then .jalr 12 else .jal 8, ⟨0, 0⟩, ⟨if indirect then 12 else 8, 0⟩,
    ⟨4, 0⟩, if indirect then .Regidx 12 else .Regidx 0, .Regidx 12, default⟩
private def jumpKind (indirect : Bool) : Fin 4 := if indirect then 3 else 2

theorem copy_then_branch_retirement (taken : Bool) : ∃ events finalState,
    events.Perm ((controlData (branchKind taken)).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (controlBefore (branchKind taken)) finalState ∧
    UnifiedReduced.Caller.RetiresCycle cells events (controlBefore (branchKind taken)) finalState (controlRow (branchKind taken))
      (SailRV32.Functions.execute_BTYPE 8 (.Regidx 0) (.Regidx 12) (if taken then .BEQ else .BNE)) := by
  refine UnifiedReduced.Caller.branch_cycle_soundness (controlAccepted _) (controlInputs _)
    (by change (0 : Nat) < 4; decide) ⟨0x40000100, by simp [controlBefore, Std.ExtDHashMap.get?_insert]⟩
    (input := branchView taken) List.mem_cons_self ?_ ?_
  · cases taken <;> constructor <;> decide +kernel
  · exact ⟨controlEntry _, List.mem_cons_self, by cases taken <;> decide +kernel,
      by cases taken <;> rfl, by change (4 : Nat) % 4 = 0; decide⟩

theorem copy_then_jump_retirement (indirect : Bool) : ∃ events finalState,
    events.Perm ((controlData (jumpKind indirect)).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (controlBefore (jumpKind indirect)) finalState ∧
    UnifiedReduced.Caller.RetiresCycle cells events (controlBefore (jumpKind indirect)) finalState (controlRow (jumpKind indirect))
      (JumpBranchSlt.Jump.execution (jumpView indirect)) := by
  refine UnifiedReduced.Caller.jump_cycle_soundness (controlAccepted _) (controlInputs _)
    (by change (0 : Nat) < 4; decide) ⟨0x40000100, by simp [controlBefore, Std.ExtDHashMap.get?_insert]⟩
    (input := jumpView indirect) ?_ List.mem_cons_self ?_ ?_
  · intro direct
    refine ⟨?_, 0, ?_, rfl⟩ <;> simp [controlBefore, Std.ExtDHashMap.get?_insert]
  · cases indirect <;> constructor <;> decide +kernel
  · exact ⟨controlEntry _, List.mem_cons_self, by cases indirect <;> decide +kernel,
      by cases indirect <;> rfl, by change (4 : Nat) % 4 = 0; decide⟩

private def memoryBits (store : Bool) : BitVec 32 := if store then 0x00c52023 else 0x00052603
private def memoryAttributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }
private def memoryBefore (store : Bool) : State :=
  let state := wordWriteState Tests.DelegationOperationEffects.before 4 (memoryBits store)
  let regs := state.regs.insert .mstatus 0
  let regs := regs.insert .cur_privilege .Machine
  let regs := regs.insert .misa (0x40000100 : BitVec 32)
  let regs := regs.insert .senvcfg 0
  let regs := regs.insert .menvcfg 0x10
  let regs := regs.insert .pmpcfg_n (Vector.replicate 64 0)
  let regs := regs.insert .pmpaddr_n (Vector.replicate 64 0)
  let regs := regs.insert .pma_regions [rv32Region memoryAttributes]
  let regs := regs.insert .mhartid 7
  let regs := regs.insert .htif_tohost_base none
  {state with regs := regs}
private def memoryEntry (store : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, memoryBits store, if store then .STORE (0, .Regidx 12, .Regidx 10, 4)
    else .LOAD (0, .Regidx 10, .Regidx 12, false, 4),
    ⟨.machine, 10, if store then 12 else 0, if store then 0 else 12,
      ⟨0, 0⟩, if store then 262144 else 131072, 0⟩⟩
private def memoryAssignment (store : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 5 then 10
  else if column = 6 ∨ column = 38 then (if store then 12 else 0)
  else if column = 7 ∨ column = 44 then (if store then 0 else 12)
  else if column = 8 ∨ column = 11 ∨ column = 50 then 0
  else if column = 28 then (if store then 0 else 1)
  else if column = 29 then (if store then 1 else 0)
  else if column = 37 ∨ column = 58 then 64
  else if column = 39 then (if store then 0 else 64)
  else if column = 45 then (if store then 64 else 0)
  else if column = 34 ∨ column = 40 ∨ column = 46 then 7
  else arithmetic 0 column
private def memoryRow (store : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, memoryAssignment store⟩
private def memoryTerminal (store : Bool) : List (MemoryToken babyBearModulus) :=
  base.machine.terminalMemory.map fun token =>
    if token.address = (Cell.register 10).addressCode then ⟨token.address, (8, 0), token.value⟩
    else if token.address = (Cell.register 12).addressCode then ⟨token.address, (if store then 9 else 10, 0), 0⟩
    else if token.address = (Cell.ram 4194304).addressCode then ⟨token.address, (if store then 10 else 9, 0), 0⟩
    else token
private def memoryData (store : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [memoryRow store, sharedCaller]
    rom := UnifiedReduced.Setup.table (memoryBefore store)
    initial := sharedCaller.start
    terminal := (memoryRow store).finish
    initialMemory := base.machine.initialMemory
    terminalMemory := memoryTerminal store }
  workers := base.workers
  program := [Tests.DelegationCaller.entry .bigint]

private theorem memoryCore (store : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (memoryAssignment store)) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (memoryBefore store))) := by
  cases store
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, memoryAssignment, arithmetic, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem memoryClocks (store : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (memoryAssignment store)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases store <;> decide +kernel

private theorem memoryChecks (store : Bool) : UnifiedReduced.Caller.RequestChecks (memoryData store) := by
  constructor
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact Verification.holds_append (memoryCore store) (memoryClocks store)
    · have same := List.mem_singleton.mp member
      subst row
      exact Verification.holds_append (callerCoreFor (memoryBefore store)) sharedTimestamps
  · intro row member
    rcases List.mem_cons.mp member with rfl | member
    · cases store <;> decide +kernel
    · have same := List.mem_singleton.mp member
      subst row
      decide +kernel
  · change ([sharedCaller.start] ++ [(memoryRow store).finish, sharedCaller.finish]).Perm
      ([(memoryRow store).finish, sharedCaller.finish] ++ [sharedCaller.start])
    exact List.perm_append_comm
  · intro row member
    have same : row = sharedCaller := by
      have callers : (memoryData store).callers = [sharedCaller] := by cases store <;> rfl
      rw [callers] at member
      exact List.mem_singleton.mp member
    subst row
    change ∃ i : Fin 1, UnifiedReduced.decoderQuery sharedAssignment =
      Delegation.Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
    exact ⟨0, by decide +kernel⟩
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerConstraints
  · exact Tests.DelegationOperationEffects.sharedAccepted.workerActive
  · exact Tests.DelegationOperationEffects.sharedAccepted.requests

private theorem memoryAccepted (store : Bool) : UnifiedReduced.Caller.MixedMemoryAccepted (memoryData store) [memoryEntry store] := by
  refine ⟨memoryChecks store, ?_, ?_⟩
  · intro row member noncaller
    rcases List.mem_cons.mp member with rfl | member
    · change ∃ i : Fin 1, (memoryRow store).decoderQuery = ([memoryEntry store].get i).query
      exact ⟨0, by cases store <;> decide +kernel⟩
    · have same := List.mem_singleton.mp member
      subst row
      exact False.elim (noncaller (by cases store <;> exact List.mem_singleton_self _))
  · cases store <;> decide +kernel

private theorem memoryInitialization (store : Bool) :
    initialImage (memoryBefore store) cells = some base.machine.initialMemory := by
  apply Trace.Proofs.image_frame (initializedAfterCode (memoryBits store))
  intro cell member value read
  cases cell with
  | ram address =>
    exact read_word_frame
      (before := wordWriteState Tests.DelegationOperationEffects.before 4 (memoryBits store))
      (after := memoryBefore store) rfl read
  | register index =>
    simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first
      | (change EStateM.Result.ok (0 : BitVec 32) _ = .ok value _ at read
         rw [← (EStateM.Result.ok.inj read).1]; rfl)
      | (change run (SailRV32.readReg .x10) _ = .ok value _ at read ⊢
         apply read_register
         simpa [memoryBefore, Std.ExtDHashMap.get?_insert] using read_register_iff.mp read)
      | (change run (SailRV32.readReg .x11) _ = .ok value _ at read ⊢
         apply read_register
         simpa [memoryBefore, Std.ExtDHashMap.get?_insert] using read_register_iff.mp read)
      | (change run (SailRV32.readReg .x12) _ = .ok value _ at read ⊢
         apply read_register
         simpa [memoryBefore, Std.ExtDHashMap.get?_insert] using read_register_iff.mp read)

private theorem memoryInputs (store : Bool) : UnifiedReduced.Caller.MixedMemoryInputs (memoryData store) [(memoryEntry store)] (memoryBefore store) [0] [4] cells := by
  refine ⟨?_, ?_, memoryInitialization store, Tests.DelegationOperationEffects.sharedInputs.distinct,
    Tests.DelegationOperationEffects.sharedInputs.aligned, rfl,
    Tests.DelegationOperationEffects.sharedInputs.tables, Tests.DelegationOperationEffects.sharedInputs.rounds⟩
  · constructor
    · have bytes : (Cell.ram 0).read (memoryBefore store) = .ok (Tests.DelegationCaller.entry .bigint).bits (memoryBefore store) :=
        read_word_frame (before := wordWriteState Tests.DelegationOperationEffects.before 4 (memoryBits store))
          (after := memoryBefore store) rfl (written_word_disjoint 4 _ (Or.inl (by decide)) (written_word_read Tests.BigintMemory.before 0 _))
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) (memoryBefore store) =
          .ok (Tests.DelegationCaller.entry .bigint).instruction (memoryBefore store) :=
        Tests.DelegationCaller.original_decoder .bigint (memoryBefore store)
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
          some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · change (4 : Nat) % 4 = 0; decide
  · have bytes : (Cell.ram 4).read (memoryBefore store) = .ok (memoryBits store) (memoryBefore store) := read_word_frame (before := wordWriteState Tests.DelegationOperationEffects.before 4 (memoryBits store))
          (after := memoryBefore store) rfl (written_word_read _ _ _)
    have decoded : run (SailRV32.Functions.encdec_backwards (memoryBits store)) (memoryBefore store) = .ok (memoryEntry store).instruction (memoryBefore store) := by
      cases store <;> with_unfolding_all rfl
    have fields : UnifiedReduced.Mixed.decoderFields (memoryEntry store).instruction = some (memoryEntry store).data := by cases store <;> with_unfolding_all rfl
    simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
      programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem memoryConfiguration (store : Bool) : FlatMemoryConfiguration (memoryBefore store) := by
  constructor
  · simp [memoryBefore, Std.ExtDHashMap.get?_insert]
  · simp [memoryBefore, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [memoryBefore, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [memoryBefore, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [memoryBefore, Std.ExtDHashMap.get?_insert]⟩
  · simp [memoryBefore, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [memoryBefore, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨memoryAttributes, by simp [memoryBefore, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨7, by simp [memoryBefore, Std.ExtDHashMap.get?_insert]⟩
  · simp [memoryBefore]

private def memoryView (store : Bool) : Airbender.WordMemory.Input :=
  ⟨store, ⟨0, 64⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, .Regidx 10, .Regidx 12, .Regidx 12, 0, default⟩
private def memoryOutput : Airbender.WordMemory.Output := ⟨⟨0, 64⟩, ⟨0, 0⟩, ⟨8, 0⟩⟩

theorem copy_then_ram_retirement [Sail.ArchSem.MemoryPlatform SailRV32.exception] (store : Bool) : ∃ events finalState,
    events.Perm ((memoryData store).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (memoryBefore store) finalState ∧
    UnifiedReduced.Caller.RetiresCycle cells events (memoryBefore store) finalState (memoryRow store)
      (Airbender.WordMemory.execution (memoryView store)) := by
  refine UnifiedReduced.Caller.ram_cycle_soundness (memoryAccepted store) (memoryInputs store)
    (by change (0 : Nat) < 4; decide) (memoryConfiguration store) ?_ ?_
    (input := memoryView store) (output := memoryOutput) (by intro mode; change SailRV32.regidx.Regidx 12 ≠ SailRV32.regidx.Regidx 0; decide) List.mem_cons_self ?_ ?_
  · intro address member
    simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
    rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
    all_goals unfold OrdinaryWordAddress
    all_goals interval_cases i <;> decide +kernel
  · intro address member
    simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
    rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
    all_goals interval_cases i <;> decide +kernel
  · cases store <;> constructor <;> decide +kernel
  · exact ⟨memoryEntry store, List.mem_cons_self, by cases store <;> decide +kernel, by cases store <;> rfl⟩

private theorem memoryCode (store : Bool) :
    UnifiedReduced.Caller.CodeProfile (memoryData store) [memoryEntry store] cells := by
  constructor
  · intro address member
    simp [Tests.DelegationOperationEffects.sharedCells, Tests.BigintMemory.cells] at member
    rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
    all_goals interval_cases i <;> decide +kernel
  · intro entry present
    have same := List.mem_singleton.mp present
    subst entry
    change (4 : Nat) < ROM.limit ∧ (4 : Nat) % 4 = 0
    decide +kernel
  · intro entry present
    have same := List.mem_singleton.mp present
    subst entry
    change (0 : Nat) < ROM.limit ∧ (0 : Nat) % 4 = 0
    decide +kernel


theorem copy_then_ram_current_fetch (store : Bool) : ∃ events finalState,
    events.Perm ((memoryData store).mixedSteps.map transferEvent) ∧
    Trace.SailHistory cells events (memoryBefore store) finalState ∧
    UnifiedReduced.Caller.CurrentFetch (memoryData store) [memoryEntry store] (memoryBefore store) cells events :=
  UnifiedReduced.Caller.current_fetch_soundness (memoryAccepted store) (memoryInputs store) (memoryCode store)

theorem copy_then_ram_caller_cycles (store : Bool) :
    UnifiedReduced.Caller.CallerCycleEffects (memoryData store) [memoryEntry store] (memoryBefore store) cells :=
  UnifiedReduced.Caller.caller_cycles_soundness (memoryAccepted store) (memoryInputs store) (memoryCode store)
    (by change (0 : Nat) < 4; decide)

private def abiAssignment (highControl : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 55 ∨ column = 56 ∨ column = 59 then (if highControl then 1 else 0)
  else if column = 66 then 0
  else if column = 1 then 5 else Tests.BigintMemory.row column
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
    (Bigint.importedConstraints Bigint.setupTable) := by
  cases highControl <;> simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, abiAssignment, Tests.BigintMemory.row,
    Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨⟨0, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨262144, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1310720, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1312768, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1316864, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1325056, by decide +kernel⟩, ?_⟩; decide +kernel)

private theorem abiTimestamps (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl)) Bigint.importedConstraintsTimestampLookups := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, abiAssignment, Tests.BigintMemory.row]
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
    WordColumns.code, WordColumns.evaluate, rawPair, abiAssignment, Tests.BigintMemory.row,
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
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
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

end Tests.UnifiedDelegation
