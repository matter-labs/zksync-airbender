import Tests.DelegationCaller
import Tests.DelegationMemory

namespace Tests.DelegationRequestTrace
open Airbender Delegation Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def caller : Trace.Row babyBearModulus PooledFamily :=
  ⟨.addSub, Tests.DelegationCaller.assignment .keccak⟩

private def machine : PooledTrace babyBearModulus where
  rows := [caller]
  rom := ⟨{ name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩
  initial := caller.start
  terminal := caller.finish
  initialMemory := []
  terminalMemory := []

private def data : Caller.RequestTrace babyBearModulus :=
  ⟨machine, Tests.DelegationMemory.data, [Tests.DelegationCaller.entry .keccak]⟩

private def before : State :=
  wordWriteState Tests.DelegationMemory.before 0 (Tests.DelegationCaller.entry .keccak).bits

private theorem caller_list : data.callers = [caller] := by rfl

theorem native_request_equal : data.calls = data.fulfillments := by
  decide +kernel

theorem accepted : Caller.RequestAccepted data := by
  constructor
  · intro row member
    simp only [data, machine, List.mem_singleton] at member
    subst row
    exact Tests.DelegationCaller.satisfies .keccak
  · intro row member
    simp only [data, machine, List.mem_singleton] at member
    subst row
    decide +kernel
  · exact List.Perm.swap _ _ []
  · intro row member
    rw [caller_list] at member
    have same : row = caller := List.mem_singleton.mp member
    subst row
    change ∃ i : Fin 1, Caller.nativeQuery caller.assignment =
      Caller.query ([Tests.DelegationCaller.entry .keccak].get i)
    exact ⟨0, Tests.DelegationCaller.query_bound .keccak⟩
  · exact Tests.DelegationMemory.accepted
  · intro row member
    have only : row = Tests.DelegationMemory.data.rows[0] := by
      simpa only [data, Tests.DelegationMemory.data, List.mem_singleton, List.getElem_cons_zero] using member
    subst row
    decide +kernel
  · rw [← native_request_equal]
    exact List.perm_append_comm

private theorem image : Caller.programImage before [0] = some data.program := by
  have bytes : (Cell.ram 0).read before =
      .ok (Tests.DelegationCaller.entry .keccak).bits before :=
    written_word_read Tests.DelegationMemory.before 0 _
  have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .keccak).bits) before =
      .ok (Tests.DelegationCaller.entry .keccak).instruction before :=
    Tests.DelegationCaller.original_decoder .keccak before
  have fields : Caller.decoderFields (Tests.DelegationCaller.entry .keccak).instruction =
      some (Tests.DelegationCaller.entry .keccak).data := Tests.DelegationCaller.metadata .keccak
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields,
    bind, Option.bind, pure]
  rfl

private theorem publicProgram : Caller.RequestInputs data before [0] :=
  ⟨image, by change 4 < timestampBase ∧ 0 < timestampBase; norm_num [timestampBase], by decide +kernel⟩

theorem bound_requests : Caller.RequestBinding data before :=
  Caller.requests_soundness (by decide) (by decide) (by decide) accepted publicProgram

theorem invocation_room_derived :
    ∀ row ∈ data.workers.rows,
      (decodeTimestamp row.assignment row.columns.invocation).Bounded ∧
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase := by
  intro row member
  exact ⟨bound_requests.clocks row member, bound_requests.clockRoom row member⟩

private theorem reject_matching (workers : List (Requests.Request babyBearModulus))
    (left : (data.calls.map Requests.Request.issued ++ workers.map Requests.Request.empty).count
      (Requests.Request.issued ⟨Requests.csr .keccak, (5, 0)⟩) = 1)
    (right : (data.calls.map Requests.Request.empty ++ workers.map Requests.Request.issued).count
      (Requests.Request.issued ⟨Requests.csr .keccak, (5, 0)⟩) = 0) :
    ¬ Requests.Matching data.calls workers := by
  intro matching
  have count := matching.count_eq (Requests.Request.issued ⟨Requests.csr .keccak, (5, 0)⟩)
  rw [left, right] at count
  contradiction

theorem missing_worker_rejected : ¬ Requests.Matching data.calls [] :=
  reject_matching [] (by decide +kernel) (by decide +kernel)

theorem changed_clock_rejected :
    ¬ Requests.Matching data.calls [⟨Requests.csr .keccak, (9, 0)⟩] :=
  reject_matching _ (by decide +kernel) (by decide +kernel)

theorem wrong_family_rejected :
    ¬ Requests.Matching data.calls [⟨Requests.csr .bigint, (5, 0)⟩] :=
  reject_matching _ (by decide +kernel) (by decide +kernel)

private theorem initialized : initialImage before Tests.DelegationMemory.cells =
    some data.workers.initial := by
  have frame : ∀ cell ∈ Tests.DelegationMemory.cells, ∀ value,
      cell.read Tests.DelegationMemory.before = .ok value Tests.DelegationMemory.before →
      cell.read before = .ok value before := by
    intro cell member value read
    cases cell with
    | register index => exact rX_register_frame (before := Tests.DelegationMemory.before) (after := before) rfl index read
    | ram address =>
      have lower : 4 ≤ address.toNat := by
        simp only [Tests.DelegationMemory.cells, List.mem_cons, List.not_mem_nil, or_false,
          Cell.ram.injEq, reduceCtorEq, false_or] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals decide +kernel
      exact written_word_disjoint 0 _ (Or.inr lower) read
  have lift : ∀ (cells : List Cell) (tokens : List (MemoryToken babyBearModulus)),
      List.Forall₂ (fun cell token => ∃ value,
        cell.read Tests.DelegationMemory.before = .ok value Tests.DelegationMemory.before ∧
        token = cell.initialToken value) cells tokens →
      (∀ cell ∈ cells, ∀ value,
        cell.read Tests.DelegationMemory.before = .ok value Tests.DelegationMemory.before →
        cell.read before = .ok value before) → initialImage before cells = some tokens := by
    intro cells tokens reads
    induction reads with
    | nil => intro _; rfl
    | @cons cell token cells tokens head tail ih =>
      intro preserved
      obtain ⟨value, read, same⟩ := head
      have current := preserved cell List.mem_cons_self value read
      have rest := ih (fun actual member => preserved actual (List.mem_cons_of_mem _ member))
      dsimp only [initialImage] at rest
      simp only [initialImage, List.mapM_cons, current, bind, Option.bind, pure, same]
      rw [rest]
  exact lift _ _ (Trace.Proofs.image_reads Tests.DelegationMemory.inputs.initialization) frame

private theorem memoryInputs : Caller.RequestMemoryInputs data before [0] Tests.DelegationMemory.cells := by
  refine ⟨publicProgram, initialized, Tests.DelegationMemory.inputs.distinct, ?_⟩
  intro cell member
  have aligned : ∀ cell ∈ Tests.DelegationMemory.cells, cell.Aligned := by
    intro cell member
    simp only [Tests.DelegationMemory.cells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  exact aligned cell member

theorem actual_worker_effects : Caller.RequestExecution data before Tests.DelegationMemory.cells :=
  Caller.request_memory_soundness (by decide) (by decide) (by decide) accepted memoryInputs

end Tests.DelegationRequestTrace
