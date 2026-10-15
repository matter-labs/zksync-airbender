import Airbender.Proofs.UnifiedReduced.HashReferenceCalls
import Airbender.Proofs.UnifiedReduced.BigintCalls
import Airbender.Proofs.UnifiedReduced.Segmentation

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

theorem full_worker_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {windows : List HashWindow} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    (commands : BigintCommands data)
    (scopes : ∀ window ∈ windows, ComputedProtocolWindowInputs data program window)
    (aligned : ∀ window ∈ windows, window.lower % 4 = 0 ∧ window.upper % 4 = 0)
    (coverage : ∀ worker ∈ data.workers.rows, worker.family ≠ .bigint →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      ∃ window ∈ windows, worker ∈ data.workers.windowRows window.lower window.upper)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ data.workers.rows)
    (live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker))
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    FullCall worker.family before after := by
  by_cases bigint : worker.family = .bigint
  · have abi := bigint_pointer_abi accepted inputs ram worker member bigint
    obtain ⟨command, binding⟩ := commands worker member bigint
    have core := accepted.workerConstraints worker member
    rcases worker with ⟨family, w⟩
    change family = .bigint at bigint
    subst family
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.clockConstraints data.workers.setup.bigint) at core
    rw [inputs.tables] at core
    have core := Verification.holds_of_sublist core
      (List.sublist_append_left (Bigint.importedConstraints Bigint.setupTable) Bigint.importedConstraintsTimestampLookups)
    exact Bigint.Call.Proofs.executes (w := w) (command := command) core abi binding history permutation observed
  · obtain ⟨window, included, inside⟩ := coverage worker member bigint live
    exact computed_window_call (by decide) (by decide) accepted inputs (scopes window included)
      (aligned window included).1 (aligned window included).2 ram inside history permutation observed

theorem full_caller_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {windows : List HashWindow}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) (commands : BigintCommands data)
    (scopes : ∀ window ∈ windows, ComputedProtocolWindowInputs data program window)
    (aligned : ∀ window ∈ windows, window.lower % 4 = 0 ∧ window.upper % 4 = 0)
    (coverage : ∀ worker ∈ data.workers.rows, worker.family ≠ .bigint →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      ∃ window ∈ windows, worker ∈ data.workers.windowRows window.lower window.upper)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.callers) :
    FullCallerCycle data initial finalState cells events row := by
  have nativeMember := List.mem_of_mem_filter member
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram nativeMember
  have floor := machine_native_clock_positive (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization nativeMember
  have positive : 0 < Delegation.Caller.startClock row := by omega
  obtain ⟨before, after, _, past, current, future⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := cycle_window_permutation (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
    effects.requests permutation nativeMember positive
  obtain ⟨worker, present, matched, grouped, localHistory⟩ :=
    caller_cycle_worker_history effects.requests member cycle current
  have readable := history_cells_readable past inputs.aligned (by
    intro cell included
    obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.initialization cell included
    exact ⟨value, read⟩)
  have noZero : ∀ event ∈ (events.filter (fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row))).filter
        (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)),
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    exact of_decide_eq_true (List.mem_filter.mp included).2
  have distinct := (grouped.map (fun event => event.2.1)).nodup_iff.mpr (by
    simpa only [List.map_map, Function.comp_def, transferEvent] using
      worker_addresses_distinct (by decide) (by decide) accepted inputs effects.requests present)
  have actual := Delegation.Proofs.atomic_observations localHistory inputs.aligned noZero readable distinct
  have observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before := by
    intro port included
    have event := grouped.mem_iff.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr
      ⟨port, by simpa using included, rfl⟩, rfl⟩)
    obtain ⟨cell, _, address, read, _⟩ := actual _ event
    exact ⟨cell, address, read⟩
  have live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker) := by
    intro zero
    exact ((effects.requests.unissued worker present).mpr zero) ⟨row, member, matched⟩
  have raw := full_worker_call accepted inputs code.ram commands scopes aligned coverage present live
    localHistory grouped observed
  have rebased := full_worker_call accepted inputs code.ram commands scopes aligned coverage present live
    (retired_state_history localHistory row.start.word.toBitVec) grouped (fun port included => by
      obtain ⟨cell, address, read⟩ := observed port included
      exact ⟨cell, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩)
  have fetch := current_fetch_of_history accepted inputs code order history
  obtain ⟨entry, included, query, pc, source⟩ := (fetch.callers row member).instruction
  have source := source before past
  have original : entry.SourceWith before Delegation.Caller.decoderFields :=
    ⟨read_word_frame (before := retiredState before row.start.word.toBitVec) (after := before) rfl source.bytes,
      (decoded_misa_frame _ source.decoded).2 _ (by simp [retiredState, Std.ExtDHashMap.get?_insert]), source.fields⟩
  have family := caller_worker_family (by decide) query matched
  exact ⟨before, after, past, current, future, entry, included, query, pc, original,
    family ▸ raw, _, family ▸ rebased, caller_pc_retirement effects.requests member⟩

end Airbender.UnifiedReduced.Caller.Proofs
