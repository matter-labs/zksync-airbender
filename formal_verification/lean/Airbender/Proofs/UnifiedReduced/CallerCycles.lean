import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.UnifiedReduced.CallerCycles
import Airbender.Proofs.UnifiedReduced.MixedFetch
import Airbender.Proofs.UnifiedReduced.UnissuedWorkers
import Airbender.Proofs.UnifiedReduced.PreparedRoundWindows
import Airbender.Proofs.Trace.Retirement

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem caller_worker_family [Fact p.Prime] (hp : FieldCapacity.AtLeast p 2048)
    {row : Trace.Row p UnifiedFamily} {entry : Delegation.Caller.ProgramEntry} {worker : Delegation.Row p}
    (query : row.decoderQuery = Delegation.Caller.query entry)
    (matched : Delegation.Requests.fulfillment worker = request row.assignment) :
    worker.family = entry.data.family := by
  have field := congrArg (fun fields : Vector (ZMod p) 9 => fields[3]) query
  cases row with
  | mk kind w =>
    cases kind
    change w 6 = (Delegation.Requests.csr entry.data.family : ZMod p) at field
    have bound : Delegation.Requests.csr entry.data.family < p := by
      cases entry.data.family <;> simp only [Delegation.Requests.csr] <;> omega
    have csr := congrArg Delegation.Requests.Request.csr matched
    change Delegation.Requests.csr worker.family = (w 6).val at csr
    rw [field, ZMod.val_natCast_of_lt bound] at csr
    have injective : Function.Injective Delegation.Requests.csr := by
      intro first last equal
      cases first <;> cases last <;> simp_all [Delegation.Requests.csr]
    exact injective csr

theorem caller_pc_retirement [Fact p.Prime] {data : RequestTrace p} {initial after : State}
    (requests : RequestBinding data initial) {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers) :
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ())
      (retiredState after row.start.word.toBitVec) = .ok () (retiredState after row.finish.word.toBitVec) := by
  cases row with
  | mk kind w =>
    cases kind
    have native := ((requests.callers _ member).sail (retiredState after (initialPC w).toBitVec)).2.2
      (retired_state_pc after _)
    have same :
        { (retiredState after (initialPC w).toBitVec) with regs :=
          ((retiredState after (initialPC w).toBitVec).regs.insert .nextPC (finalPC w).toBitVec).insert .PC (finalPC w).toBitVec } =
        retiredState after (finalPC w).toBitVec := by
      have registers :
          (((after.regs.insert .nextPC (initialPC w).toBitVec).insert .PC (initialPC w).toBitVec).insert
            .nextPC (finalPC w).toBitVec).insert .PC (finalPC w).toBitVec =
          (after.regs.insert .nextPC (finalPC w).toBitVec).insert .PC (finalPC w).toBitVec := by
        apply Std.ExtDHashMap.ext_get?
        intro register
        by_cases pc : register = .PC
        · subst register; simp
        · by_cases next : register = .nextPC
          · subst register; simp [Std.ExtDHashMap.get?_insert]
          · simp [Std.ExtDHashMap.get?_insert, Ne.symm pc, Ne.symm next]
      exact congrArg (fun regs => { after with regs := regs }) registers
    change run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ())
      (retiredState after (initialPC w).toBitVec) = .ok ()
        { (retiredState after (initialPC w).toBitVec) with regs :=
          ((retiredState after (initialPC w).toBitVec).regs.insert .nextPC (finalPC w).toBitVec).insert .PC (finalPC w).toBitVec } at native
    rw [same] at native
    simpa only [initialPC, finalPC] using native

theorem caller_cycle_observations [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial before after : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (requests : RequestBinding data initial)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers)
    {earlier events : List MemoryAccess} (permutation : events.Perm (data.cycleSteps row |>.map transferEvent))
    (past : SailHistory cells earlier initial before) (current : SailHistory cells events before after) :
    ∃ worker ∈ data.workers.rows, Delegation.Requests.fulfillment worker = request row.assignment ∧
      ∀ port ∈ worker.ports, ∃ cell ∈ cells,
        cell.addressCode = port.address.code worker.assignment ∧
        cell.read (retiredState before row.start.word.toBitVec) =
          .ok (readToken worker.assignment port).word.toBitVec (retiredState before row.start.word.toBitVec) ∧
        cell.read (retiredState after row.finish.word.toBitVec) =
          .ok (worker.writeToken port).word.toBitVec (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨worker, present, same, grouped, history⟩ := caller_cycle_worker_history requests member permutation current
  have readable := history_cells_readable past inputs.aligned (by
    intro cell included
    obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.initialization cell included
    exact ⟨value, read⟩)
  have noZero : ∀ event ∈ events.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)),
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    exact of_decide_eq_true (List.mem_filter.mp included).2
  have unique : ((events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).map
      fun event => event.2.1).Nodup := (grouped.map (fun event => event.2.1)).nodup_iff.mpr (by
    simpa only [List.map_map, Function.comp_def, transferEvent] using
      worker_addresses_distinct hp inverse accepted inputs requests present)
  have actual := Delegation.Proofs.atomic_observations history inputs.aligned noZero readable unique
  refine ⟨worker, present, same, ?_⟩
  intro port included
  have event := grouped.mem_iff.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr
    ⟨port, by simpa using included, rfl⟩, rfl⟩)
  obtain ⟨cell, cellMember, address, read, written⟩ := actual _ event
  change cell.addressCode = port.address.code worker.assignment at address
  change cell.read before = .ok (readToken worker.assignment port).word.toBitVec before at read
  change cell.read after = .ok (worker.writeToken port).word.toBitVec after at written
  have read := cell_read_PC cell (cell_read_nextPC cell read row.start.word.toBitVec) row.start.word.toBitVec
  have written := cell_read_PC cell (cell_read_nextPC cell written row.finish.word.toBitVec) row.finish.word.toBitVec
  exact ⟨cell, cellMember, address, read, written⟩

theorem native_caller_cycles_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState) :
    ∀ row ∈ data.callers, CallerCycle data initial finalState cells events row := by
  have fetch := current_fetch_of_history accepted inputs code order history
  intro row member
  have nativeMember := List.mem_of_mem_filter member
  have floor := machine_native_clock_positive (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization nativeMember
  have positive : 0 < Delegation.Caller.startClock row := by omega
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram nativeMember
  obtain ⟨before, after, _, past, current, future⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := cycle_window_permutation (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
    effects.requests permutation nativeMember positive
  obtain ⟨entry, present, query, pc, source⟩ := (fetch.callers row member).instruction
  obtain ⟨worker, workerMember, matched, observations⟩ := caller_cycle_observations (by decide) (by decide)
    accepted inputs effects.requests member cycle past current
  exact ⟨before, after, past, current, future,
    ⟨entry, present, query, pc, source before past, worker, workerMember, matched,
      caller_worker_family (by decide) query matched, effects.operations worker workerMember, observations⟩,
    caller_pc_retirement effects.requests member⟩


theorem native_caller_cycles
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) :
    CallerCycleEffects data program initial cells := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  exact ⟨effects.requests, events, finalState, permutation, order, history,
    current_fetch_of_history accepted inputs code order history,
    native_caller_cycles_at accepted inputs code effects permutation order history, terminal⟩


/-- Compatibility entry retaining the earlier explicit clock premise. -/
theorem caller_cycles
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) (started : 0 < (timeOfPair data.machine.initial.timestamp).value) :
    CallerCycleEffects data program initial cells := by
  exact (fun _ : 0 < (timeOfPair data.machine.initial.timestamp).value =>
    native_caller_cycles accepted inputs code) started

theorem prepared_round_caller_cycles
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {flags : Fin 8} {lower : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : PreparedRoundInputs data initial ca oa cells program flags lower) (first : lower % 4 = 0)
    (code : CodeProfile data program cells) (started : 0 < (timeOfPair data.machine.initial.timestamp).value) :
    CallerCycleEffects data program initial cells :=
  caller_cycles accepted (prepared_round_memory_inputs (by decide) (by decide) accepted inputs first) code started

end Airbender.UnifiedReduced.Caller.Proofs
