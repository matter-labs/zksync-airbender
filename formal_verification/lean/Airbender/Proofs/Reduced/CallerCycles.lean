import Airbender.Proofs.Reduced.CallerSources

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Native workers retire the caller at its exact shared-history boundaries. -/
theorem native_full_caller_cycle_at
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program initial ca oa cells)
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (workerFamilies : ∀ worker ∈ data.workers.rows, worker.family = .blakeRound)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (initialPositive : 0 < (timeOfPair data.machine.initial.timestamp).value)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ data.callers) :
    FullCallerCycle data initial finalState cells events row := by
  have nativeMember := List.mem_of_mem_filter member
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram nativeMember
  have floor := machine_clock_floor (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram nativeMember
  have positive : 0 < Delegation.Caller.startClock row := lt_of_lt_of_le initialPositive floor
  have slots := worker_schedule (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram effects.requests
  obtain ⟨before, after, _, past, current, future⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := cycle_window_permutation (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
    effects.requests slots permutation nativeMember positive
  obtain ⟨worker, present, matched, grouped, localHistory⟩ :=
    caller_cycle_worker_history effects.requests slots member cycle current
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
      worker_addresses_distinct accepted inputs effects present)
  have actual := Delegation.Proofs.atomic_observations localHistory inputs.aligned noZero readable distinct
  have observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before := by
    intro port included
    have event := grouped.mem_iff.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr
      ⟨port, by simpa using included, rfl⟩, rfl⟩)
    obtain ⟨cell, _, address, read, _⟩ := actual _ event
    exact ⟨cell, address, read⟩
  have raw := native_round_worker_call accepted inputs effects ram controls present (workerFamilies _ present) localHistory grouped observed
  have rebased := native_round_worker_call accepted inputs effects ram controls present (workerFamilies _ present)
    (retired_state_history localHistory row.start.word.toBitVec) grouped (fun port included => by
      obtain ⟨cell, address, read⟩ := observed port included
      exact ⟨cell, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩)
  obtain ⟨entry, included, query, pc, source⟩ :=
    caller_source_readonly (by decide) accepted.toRequestChecks inputs.publicProgram code readonly member past
  have family := caller_worker_family (by decide) query matched
  exact ⟨before, after, past, current, future, entry, included, query, pc, source,
    family ▸ raw, _, family ▸ rebased, caller_pc_retirement effects.requests member⟩



end Airbender.AddSub.Modular.External.Caller.Proofs
