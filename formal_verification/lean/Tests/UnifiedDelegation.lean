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

end Tests.UnifiedDelegation
