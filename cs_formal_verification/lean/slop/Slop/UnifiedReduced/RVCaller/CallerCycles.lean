import Human.Trace.UnifiedReduced.RVCallerCycles
import Slop.UnifiedReduced.RVCaller.PreparedRoundWindows
import Slop.Delegation.RVCallLink

/-! RV siblings of `MixedFetch.lean` and `CallerCycles.lean`: every row fetches its public RV entry in every reachable
    pre-state (the ROM image, `rom`, is never changed by an RV history), and every caller cycle has actual RV states,
    its matched worker's port reads at the cycle boundaries, the spec's PC retirement, and `RV.step` at its pre-state
    equal to `RV.exec` of the decoded `.delegate k`. -/

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_entry_rom_frame {Kind : Type} (projection : RV.Instr → Option (DecoderData Kind))
    {s t : RV.State} (rom : t.rom = s.rom) (pc : BitVec 32) :
    rvProgramEntryWith projection t pc = rvProgramEntryWith projection s pc := by
  unfold rvProgramEntryWith
  rw [rom]

theorem rv_image_entry_source {Kind : Type} {projection : RV.Instr → Option (DecoderData Kind)}
    {before : RV.State} {addresses : List (BitVec 32)} {program : List (Trace.RVProgramEntry Kind)}
    (image : rvProgramImageWith projection before addresses = some program)
    {entry : Trace.RVProgramEntry Kind} (present : entry ∈ program) :
    rvProgramEntryWith projection before entry.pc = some entry := by
  obtain ⟨pc, _, built⟩ := mem_rvProgramImage image entry present
  obtain ⟨pcEq, _⟩ := rvProgramEntryWith_some built
  rw [pcEq]
  exact built

theorem rv_current_fetch_of_history
    {data : RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry}
    {initial : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program initial ca oa cells)
    {events : List MemoryAccess} {finalState : RV.State}
    (order : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events initial finalState) :
    RVCurrentFetch data program initial cells events := by
  have reachable (row : Trace.Row babyBearModulus UnifiedFamily) (member : row ∈ data.machine.rows) :
      ∃ before, RVHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before := by
    have clocks := rv_machine_clock_facts (by decide) (by decide) accepted.toRVRequestChecks inputs.publicProgram member
    obtain ⟨before, after, _, past, _, _⟩ := rv_history_window order history
      (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
    exact ⟨before, past⟩
  have frame {Kind : Type} {projection : RV.Instr → Option (DecoderData Kind)} {entry : Trace.RVProgramEntry Kind}
      (source : rvProgramEntryWith projection initial entry.pc = some entry) (clock : Nat) :
      ∀ before, RVHistory cells (events.filter fun event => decide (event.1 ≤ clock)) initial before →
        rvProgramEntryWith projection before entry.pc = some entry := by
    intro before past
    rw [rv_entry_rom_frame projection (Delegation.Proofs.rv_history_fields past).2.1]
    exact source
  refine ⟨?_, ?_⟩
  · intro row member ordinary
    obtain ⟨entry, present, _, query⟩ := rv_decoder_member (accepted.ordinaryDecoded row member ordinary)
    have pc : row.start.word.toBitVec = entry.pc := rv_query_pc (by decide) query
    exact ⟨reachable row member, entry, present, query, pc,
      frame (rv_image_entry_source inputs.ordinaryProgram present) row.clock⟩
  · intro row member
    have decoded := accepted.decoded row member
    change ∃ i : Fin data.program.length, row.decoderQuery = rvCallerQuery (data.program.get i) at decoded
    obtain ⟨i, query⟩ := decoded
    let entry := data.program.get i
    have present : entry ∈ data.program := List.get_mem _ _
    have pcWord := rv_caller_query_pc_word (by decide) query
    have pc : row.start.word.toBitVec = entry.pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
    exact ⟨reachable row (List.mem_of_mem_filter member), entry, present, query, pc,
      frame (rv_caller_entry inputs.publicProgram.image present).1 row.clock⟩

theorem rv_caller_worker_family [Fact p.Prime] (hp : 2048 ≤ p)
    {row : Trace.Row p UnifiedFamily} {entry : RVCallerEntry} {worker : Delegation.Row p}
    (query : row.decoderQuery = rvCallerQuery entry)
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

theorem rv_caller_pc_retirement [Fact p.Prime] {data : RVRequestTrace p} {initial after : RV.State}
    (requests : RVRequestBinding data initial) {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers) :
    (after.setPC row.start.word.toBitVec).nextInstr = after.setPC row.finish.word.toBitVec := by
  cases row with
  | mk kind w =>
    cases kind
    have advance := (requests.callers _ member).pc.2.2
    change (after.setPC (initialPC w).toBitVec).nextInstr = after.setPC (finalPC w).toBitVec
    rw [advance]
    rfl

theorem rv_caller_cycle_observations [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {initial before after : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program initial ca oa cells)
    (requests : RVRequestBinding data initial)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers)
    {events : List MemoryAccess} (permutation : events.Perm (data.cycleSteps row |>.map transferEvent))
    (current : RVHistory cells events before after)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0) :
    ∃ worker ∈ data.workers.rows, Delegation.Requests.fulfillment worker = request row.assignment ∧
      ∀ port ∈ worker.ports, ∃ cell ∈ cells,
        cell.addressCode = port.address.code worker.assignment ∧
        cell.readRV before = some (readToken worker.assignment port).word.toBitVec ∧
        cell.readRV after = some (worker.writeToken port).word.toBitVec := by
  obtain ⟨worker, present, same, grouped, history⟩ :=
    rv_caller_cycle_worker_history requests member permutation current zero
  have noZero : ∀ event ∈ events.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)),
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    exact of_decide_eq_true (List.mem_filter.mp included).2
  have unique : ((events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).map
      fun event => event.2.1).Nodup := (grouped.map (fun event => event.2.1)).nodup_iff.mpr (by
    simpa only [List.map_map, Function.comp_def, transferEvent] using
      rv_worker_addresses_distinct hp inverse accepted inputs requests present)
  have actual := Delegation.Proofs.rv_atomic_observations history inputs.aligned noZero unique
  refine ⟨worker, present, same, ?_⟩
  intro port included
  have event := grouped.mem_iff.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr
    ⟨port, by simpa using included, rfl⟩, rfl⟩)
  obtain ⟨cell, cellMember, address, read, written⟩ := actual _ event
  exact ⟨cell, cellMember, address, read, written⟩

theorem rv_caller_cycles
    {data : RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {initial : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value) :
    RVCallerCycleEffects data program initial cells := by
  have effects := rv_mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  have fetch := rv_current_fetch_of_history accepted inputs order history
  have zeroWrites := rv_mixed_zero_writes (by decide) (by decide) accepted inputs
  refine ⟨effects.requests, events, finalState, permutation, order, history, fetch, ?_, terminal⟩
  intro row member
  have nativeMember := List.mem_of_mem_filter member
  have positive : 0 < Delegation.Caller.startClock row := lt_of_lt_of_le started
    (rv_machine_clock_floor (by decide) (by decide) accepted.toRVRequestChecks inputs.publicProgram nativeMember)
  have clocks := rv_machine_clock_facts (by decide) (by decide) accepted.toRVRequestChecks inputs.publicProgram
    nativeMember
  obtain ⟨before, after, _, past, current, future⟩ := rv_history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := rv_cycle_window_permutation (by decide) (by decide) accepted.toRVRequestChecks inputs.publicProgram
    effects.requests permutation nativeMember positive
  have zero : ∀ event ∈ events.filter (fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)),
      event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0 :=
    fun event member => rv_events_zero permutation zeroWrites event (List.mem_of_mem_filter member)
  obtain ⟨entry, present, query, pc, source⟩ := (fetch.callers row member).instruction
  obtain ⟨worker, workerMember, matched, observations⟩ := rv_caller_cycle_observations (by decide) (by decide)
    accepted inputs effects.requests member cycle current zero
  have decoded := (rv_caller_entry inputs.publicProgram.image present).2.2.2
  have step : RV.step (before.setPC entry.pc) =
      RV.exec (before.setPC entry.pc) (.delegate (familyKind entry.data.family)) :=
    rv_caller_step inputs.publicProgram.image present
      ((Delegation.Proofs.rv_history_fields past).2.1) rfl
  exact ⟨before, after, past, current, future,
    ⟨entry, present, query, pc, source before past, decoded, step, worker, workerMember, matched,
      rv_caller_worker_family (by decide) query matched, effects.operations worker workerMember, observations⟩,
    rv_caller_pc_retirement effects.requests member⟩

theorem rv_prepared_round_caller_cycles
    {data : RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {initial : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {flags : Fin 8} {lower : Nat}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVPreparedRoundInputs data initial ca oa cells program flags lower) (first : lower % 4 = 0)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value) :
    RVCallerCycleEffects data program initial cells :=
  rv_caller_cycles accepted (rv_prepared_round_memory_inputs (by decide) (by decide) accepted inputs first) started

end Airbender.UnifiedReduced.Caller.Proofs
