import Airbender.Proofs.UnifiedReduced.PathCalls
import Airbender.Proofs.UnifiedReduced.PathCallABI
import Airbender.Proofs.UnifiedReduced.FullComposition
import Airbender.Proofs.UnifiedReduced.MixedCycleComposition

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Native complete participation and public occurrence preparation derive
    every local complete reference call, with the existing bigint F02 binding
    and the existing successful G block-separation ABI retained. -/
theorem path_planned_worker_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {plans : List (PathCallPlan data program)} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data initial ca oa cells program plans)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    (commands : BigintCommands data)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ data.workers.rows)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    FullCall worker.family before after := by
  have memory := path_calls_memory_inputs (by decide) (by decide) accepted inputs
  obtain ⟨plan, _, matched⟩ := path_worker_call_plan (by decide) accepted.toRequestChecks inputs member
  have binding : match plan.position with
      | .bigint => worker.family = .bigint
      | .hash position => position.NativeBinding worker := by
    cases form : plan.position with
    | bigint =>
      simpa only [form, PathCallPosition.family] using matched.1.symm
    | hash position =>
      exact path_plan_hash_binding (by decide) (by decide) accepted inputs position form member matched
  have pointers : PathCallPosition.PointerBinding plan.position worker := by
    cases form : plan.position with
    | bigint => trivial
    | hash position =>
      cases position with
      | mk span index =>
        cases span with
        | blakeG reduced =>
          exact path_plan_g_pointer_binding (by decide) (by decide) accepted inputs form member matched
        | blakeRound flags => trivial
        | keccak => trivial
  exact path_worker_call accepted memory ram commands plan.position member binding pointers history permutation observed

/-- One actual caller cycle derives its full independent call and original
    retirement from public code, computed preparation and shared native history.
    Ordinary gaps retain their actual register/link/RAM mutations. -/
theorem path_full_caller_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data initial ca oa cells program plans)
    (code : CodeProfile data program cells) (commands : BigintCommands data)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.callers) :
    FullCallerCycle data initial finalState cells events row := by
  have memory := path_calls_memory_inputs (by decide) (by decide) accepted inputs
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
      worker_addresses_distinct (by decide) (by decide) accepted memory effects.requests present)
  have actual := Delegation.Proofs.atomic_observations localHistory inputs.aligned noZero readable distinct
  have observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before := by
    intro port included
    have event := grouped.mem_iff.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr
      ⟨port, by simpa using included, rfl⟩, rfl⟩)
    obtain ⟨cell, _, address, read, _⟩ := actual _ event
    exact ⟨cell, address, read⟩
  have raw := path_planned_worker_call accepted inputs code.ram commands present localHistory grouped observed
  have rebased := path_planned_worker_call accepted inputs code.ram commands present
    (retired_state_history localHistory row.start.word.toBitVec) grouped (fun port included => by
      obtain ⟨cell, address, read⟩ := observed port included
      exact ⟨cell, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩)
  have fetch := current_fetch_of_history accepted memory code order history
  obtain ⟨entry, included, query, pc, source⟩ := (fetch.callers row member).instruction
  have source := source before past
  have original : entry.SourceWith before Delegation.Caller.decoderFields :=
    ⟨read_word_frame (before := retiredState before row.start.word.toBitVec) (after := before) rfl source.bytes,
      (decoded_misa_frame _ source.decoded).2 _ (by simp [retiredState, Std.ExtDHashMap.get?_insert]), source.fields⟩
  have family := caller_worker_family (by decide) query matched
  exact ⟨before, after, past, current, future, entry, included, query, pc, original,
    family ▸ raw, _, family ▸ rebased, caller_pc_retirement effects.requests member⟩

/-- Whole actual-path execution with branches, jumps and repeated-PC loops.
    Native controller transport and every local family reference are derived;
    the final state realizes the exact native terminal PC and all tracked cells. -/
theorem path_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data initial ca oa cells program plans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) :
    Realizes (FullStep program data.program) data.machine initial cells := by
  have memory := path_calls_memory_inputs (by decide) (by decide) accepted inputs
  have effects := mixed_memory_effects accepted memory
  have ledger := ExternalBoundary.Requests.Proofs.native_binding accepted.toRequestChecks effects.requests
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  exact full_execution_at accepted memory profile.code effects.requests pc ledger permutation order history
    (fun _ member ordinary => ordinary_cycle_at accepted memory profile effects permutation order history member ordinary)
    (fun _ member => path_full_caller_cycle_at accepted inputs profile.code commands effects permutation order history member)
    terminal

end Airbender.UnifiedReduced.Caller.Proofs
