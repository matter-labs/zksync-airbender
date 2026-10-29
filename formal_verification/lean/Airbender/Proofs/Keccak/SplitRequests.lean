import Airbender.Review.Trace.Workers.Keccak.SplitRequests
import Airbender.Proofs.Delegation.RequestTrace
import Airbender.Proofs.Trace.Program

namespace Airbender.Keccak.Split.Native.Proofs
open Airbender.Trace Airbender.Delegation Airbender.Arithmetic
  Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem caller_member [Fact p.Prime] {data : RequestTrace p}
    {row : Airbender.Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    row ∈ data.machine.rows ∧ row.family = .addSub := by
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  have family : row.family = .addSub := by
    cases equal : row.family <;> simp_all [RequestTrace.callers]
  exact ⟨present, family⟩

/-- Exact native decoder matching and the public Sail image identify the
original split CSR instruction, including its complete virtual address. -/
theorem public_source [Fact p.Prime]
    {data : RequestTrace p} (accepted : RequestChecks data)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data before addresses)
    {row : Airbender.Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    ∃ entry ∈ data.program,
      entry.SourceWith before Split.Caller.decoderFields ∧
      Delegation.Caller.nativeQuery row.assignment = Split.Caller.query entry := by
  have decoded := accepted.decoded row member
  change ∃ index : Fin data.program.length,
    Delegation.Caller.nativeQuery row.assignment = Split.Caller.query (data.program.get index)
    at decoded
  obtain ⟨index, equal⟩ := decoded
  exact ⟨data.program.get index, List.get_mem _ _,
    Airbender.Trace.Proofs.run_program_sources inputs.image _ (List.get_mem _ _), equal⟩

/-- A full-width native decoder query cannot alias a different split CSR in
any field large enough for the project's sixteen-bit decoder limbs. -/
theorem caller_csr_of_query [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 65536)
    {w : Nat → ZMod p} {entry : Split.Caller.ProgramEntry}
    (equal : Delegation.Caller.nativeQuery w = Split.Caller.query entry) :
    (Requests.caller w).csr = entry.data.family.csr := by
  have key := congrArg (fun values : Vector (ZMod p) 9 => values[3]) equal
  change w AddSub.importedConstraintsDecoderColumns.rs2 =
    (entry.data.family.csr : ZMod p) at key
  change (w AddSub.importedConstraintsDecoderColumns.rs2).val = entry.data.family.csr
  rw [key, ZMod.val_natCast_of_lt]
  cases entry.data.family <;> norm_num [Split.Kind.csr] at hp ⊢ <;> omega

private theorem query_pc [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 65536)
    {w : Nat → ZMod p} {entry : Split.Caller.ProgramEntry}
    (equal : Delegation.Caller.nativeQuery w = Split.Caller.query entry) :
    Delegation.Caller.initialPC w = Arithmetic.Word.ofBitVec entry.pc := by
  have low := congrArg (fun values : Vector (ZMod p) 9 => values[0]) equal
  have high := congrArg (fun values : Vector (ZMod p) 9 => values[1]) equal
  change w 0 = ((Arithmetic.Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w 1 = ((Arithmetic.Word.ofBitVec entry.pc).hi : ZMod p) at high
  change (⟨(w 0).val, (w 1).val⟩ : Arithmetic.Word) =
    Arithmetic.Word.ofBitVec entry.pc
  exact Airbender.Trace.Proofs.word_of_pc_query hp low high

/-- The imported ADD/SUB caller equations advance the sourced split CSR's PC
by four, with canonical final limbs and the original Sail PC retirement. -/
theorem caller_pc_binding [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 196608)
    (inverse : SerializedInverse.Limb16 p)
    {data : RequestTrace p} (accepted : RequestChecks data)
    {before : State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data before addresses)
    {row : Airbender.Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    CallerPCBinding row.assignment before data.program := by
  obtain ⟨present, family⟩ := caller_member member
  have core := accepted.machineConstraints row present
  simp only [Airbender.Trace.Row.constraints, family, CircuitLayout.constraints] at core
  have constraints : FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) AddSub.importedConstraints :=
    Verification.holds_of_sublist core
      (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
  obtain ⟨entry, entryMember, source, equal⟩ := public_source accepted inputs member
  have initial := query_pc (by omega) equal
  have mapping : AddSub.PCMapping (Delegation.Caller.initialPC row.assignment)
      (Delegation.Caller.finalPC row.assignment) row.assignment := by
    constructor
    · change row.assignment 0 = ((row.assignment 0).val : ZMod p)
      exact (ZMod.natCast_zmod_val _).symm
    · change row.assignment 1 = ((row.assignment 1).val : ZMod p)
      exact (ZMod.natCast_zmod_val _).symm
    · rfl
    · rfl
  have result := AddSub.Proofs.pc_successor hp inverse constraints mapping
    (initial.symm ▸ Word.ofBitVec_bound entry.pc)
  refine ⟨⟨entry, entryMember, source, initial⟩,
    AddSub.Proofs.pc_bounds constraints mapping, result.2.2, ?_⟩
  intro state read
  have prepare := initialize_next_pc read
  rw [run_bind_of_ok _ _ _ _ _ prepare]
  have finish := tick_pc_run
    (state := { state with regs := state.regs.insert .nextPC ((Delegation.Caller.initialPC row.assignment).toBitVec + 4) })
    (pc := (Delegation.Caller.initialPC row.assignment).toBitVec + 4) (by simp)
  simpa only [result.2.2] using finish

/-- Native state clocks are unique, so the issued split CSR timestamps are
unique even when the physical worker rows are presented out of order. -/
theorem caller_clocks_unique [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} (accepted : RequestChecks data)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data before addresses) :
    (data.calls.map Requests.Request.time).Nodup := by
  have clocks := Airbender.Trace.Proofs.state_clock_inputs hp inverse
    accepted.machineConstraints accepted.states inputs.initialClock inputs.initialAligned
  let rank := fun row : Airbender.Trace.Row p PooledFamily =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have allUnique := Airbender.Trace.Proofs.state_clocks_unique hp inverse
    accepted.machineConstraints accepted.states inputs.initialClock inputs.initialAligned
  have callerUnique : (data.callers.map rank).Nodup :=
    allUnique.sublist ((show data.callers.Sublist data.machine.rows from List.filter_sublist).map rank)
  simp only [RequestTrace.calls, List.map_map, Function.comp_def]
  apply Requests.Proofs.shifted_times_unique callerUnique
  intro row member
  obtain ⟨present, family⟩ := caller_member member
  have clock := clocks row present
  simp only [Airbender.Trace.Row.columns, family, CircuitLayout.columns] at clock
  have one : Requests.callerPort.clock.offset = 1 := rfl
  simpa only [Requests.caller, one, rank, Airbender.Trace.Row.columns, family,
    CircuitLayout.columns, decodeTimestamp, timeOfPair, rawPair] using
    (Airbender.Trace.Proofs.write_time (by omega)
      (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

/-- The exact virtual-token permutation matches every nonzero split caller to
a worker of the same full-width CSR and invocation clock. Worker clock bounds
and no low-limb rollover follow from the public initial clock. -/
theorem request_clock_binding [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} (accepted : RequestChecks data)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data before addresses) :
    RequestClockBinding data := by
  have machineClocks := Airbender.Trace.Proofs.state_clock_inputs hp inverse
    accepted.machineConstraints accepted.states inputs.initialClock inputs.initialAligned
  have clocks : ∀ row ∈ data.callers,
      (timeOfPair (Requests.caller row.assignment).time).Bounded ∧
      Requests.Live (Requests.caller row.assignment) ∧
      (timeOfPair (Requests.caller row.assignment).time).lo + 2 < timestampBase := by
    intro row member
    obtain ⟨present, family⟩ := caller_member member
    have facts := machineClocks row present
    simp only [Airbender.Trace.Row.columns, family, CircuitLayout.columns] at facts
    exact Delegation.Caller.Proofs.caller_clock (by omega) facts.1 facts.2
  have unique := caller_clocks_unique hp inverse accepted inputs
  have pool := Requests.Proofs.bounded_pool accepted.requests
    (by
      intro call present
      obtain ⟨row, member, rfl⟩ := List.mem_map.mp present
      exact clocks row member) unique
  refine ⟨pool.1, ?_, ?_, ⟨unique, pool.2.2⟩⟩
  · intro worker present
    exact (pool.2.1 _ (List.mem_map.mpr ⟨worker, present, rfl⟩)).1
  · intro worker present
    exact (pool.2.1 _ (List.mem_map.mpr ⟨worker, present, rfl⟩)).2

/-- Each issued split caller has exactly one physical worker row at its
full-width CSR and invocation clock. -/
theorem unique_issued_worker [Fact p.Prime]
    {data : RequestTrace p} (binding : RequestClockBinding data)
    {row : Airbender.Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    ∃! worker, worker ∈ data.workers.rows ∧
      worker.fulfillment data.workers.cached = Requests.caller row.assignment := by
  let call := Requests.caller row.assignment
  have called : call ∈ data.calls := List.mem_map.mpr ⟨row, member, rfl⟩
  have admitted := binding.fulfilled.mem_iff.mp called
  have live : Requests.Live call := of_decide_eq_true (List.mem_filter.mp admitted).2
  obtain ⟨worker, present, same⟩ := List.mem_map.mp (List.mem_filter.mp admitted).1
  let issued := data.workers.rows.filter fun worker =>
    decide (Requests.Live (worker.fulfillment data.workers.cached))
  have issuedUnique :
      (issued.map fun worker => (worker.fulfillment data.workers.cached).time).Nodup := by
    simpa only [List.filter_map, List.map_map, Function.comp_def, issued,
      RequestTrace.fulfillments]
      using (binding.fulfilled.map Requests.Request.time).nodup_iff.mp
        binding.invocations.1
  have chosen : worker ∈ issued := List.mem_filter.mpr
    ⟨present, by rw [same]; exact decide_eq_true live⟩
  refine ⟨worker, ⟨present, same⟩, ?_⟩
  intro other otherMatch
  have included : other ∈ issued := List.mem_filter.mpr
    ⟨otherMatch.1, by rw [otherMatch.2]; exact decide_eq_true live⟩
  exact List.inj_on_of_nodup_map issuedUnique included chosen
    ((congrArg Requests.Request.time otherMatch.2).trans
      (congrArg Requests.Request.time same).symm)

private theorem split_csr_injective : Function.Injective Split.Kind.csr := by
  intro first last equal
  cases first <;> cases last <;> simp_all [Split.Kind.csr]

/-- Public Sail decoding fixes the worker kind of a matched split invocation.
Neither the native caller nor the worker witness can swap parity, theta/rho or
chi5 while retaining the full-width virtual CSR request. -/
theorem public_caller_worker_kind [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 65536)
    {data : RequestTrace p} (accepted : RequestChecks data)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data before addresses)
    (binding : RequestClockBinding data)
    {row : Airbender.Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    ∃ entry ∈ data.program, entry.SourceWith before Split.Caller.decoderFields ∧
      ∃ worker ∈ data.workers.rows,
        worker.kind = entry.data.family ∧
        worker.fulfillment data.workers.cached = Requests.caller row.assignment := by
  obtain ⟨entry, entryMember, source, query⟩ := public_source accepted inputs member
  obtain ⟨worker, ⟨workerMember, same⟩, _⟩ := unique_issued_worker binding member
  have csr : worker.kind.csr = entry.data.family.csr := by
    calc
      worker.kind.csr = (worker.fulfillment data.workers.cached).csr := rfl
      _ = (Requests.caller row.assignment).csr := congrArg Requests.Request.csr same
      _ = entry.data.family.csr := caller_csr_of_query hp query
  exact ⟨entry, entryMember, source, worker, workerMember,
    split_csr_injective csr, same⟩

end Airbender.Keccak.Split.Native.Proofs
