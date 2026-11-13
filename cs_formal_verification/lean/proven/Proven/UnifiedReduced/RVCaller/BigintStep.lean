module
public import Proven.UnifiedReduced.RVCaller.CallerCycles
public import Proven.Bigint.RVCallStep
public import Proven.Trace.RVPooledRow

@[expose] public section
namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic

/-- A fetched bigint caller takes one actual RV step from its cut in the shared history. -/
theorem rv_bigint_caller_cycle
    {data : RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry}
    {initial before after : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVMixedMemoryInputs data program initial ca oa cells)
    (requests : RVRequestBinding data initial)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.callers)
    {entry : Delegation.Caller.RVProgramEntry}
    (query : row.decoderQuery = Delegation.Caller.rvQuery entry)
    (family : entry.data.family = .bigint) (source : Delegation.Caller.RVSource before entry)
    {events : List MemoryAccess} (permutation : events.Perm (data.cycleSteps row |>.map transferEvent))
    (current : RVHistory cells events before after)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧
      RV.Same next (after.setPC row.finish.word.toBitVec) := by
  obtain ⟨worker, present, matched, grouped, history, observations⟩ :=
    rv_caller_cycle_observations_and_history (by decide) (by decide)
      accepted inputs requests member permutation current zero
  have selected := (rv_caller_worker_family (by decide) query matched).trans family
  obtain ⟨kind, w⟩ := worker
  change kind = .bigint at selected
  subst kind
  have holds := accepted.workerConstraints _ present
  rw [inputs.tables] at holds
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Bigint.clockConstraints Bigint.setupTable) at holds
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (Bigint.importedConstraints Bigint.setupTable)
      Bigint.importedConstraintsTimestampLookups)
  have readPC (cell : Cell) (state : RV.State) (pc : RV.Word) :
      cell.readRV (state.setPC pc) = cell.readRV state := by cases cell <;> rfl
  have ports : ∀ port ∈ Bigint.importedConstraintsMemoryPorts, ∃ cell ∈ cells,
      cell.addressCode = port.address.code w ∧
      cell.readRV (before.setPC entry.pc) = some (memoryWord (port.readCode w)) ∧
      cell.readRV (after.setPC entry.pc) = some (memoryWord (port.writeCode w)) := by
    intro port included
    obtain ⟨cell, cellMember, address, read, written⟩ := observations port included
    exact ⟨cell, cellMember, address, by simpa only [readPC, readToken, MemoryToken.word, memoryWord] using read,
      by simpa only [readPC, Delegation.Row.writeToken, MemoryToken.word, memoryWord] using written⟩
  have distinct := rv_worker_addresses_distinct (by decide) (by decide) accepted inputs requests present
  obtain ⟨next, called, same⟩ := Bigint.Proofs.rv_bigint_call_local core ports distinct inputs.aligned
    (rv_history_with_pc history entry.pc) grouped
  have pcWord := rv_caller_query_pc_word (by decide) query
  have pc : row.start.word.toBitVec = entry.pc :=
    (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
  have retirement := rv_caller_pc_retirement requests (after := after) member
  rw [pc] at retirement
  change after.setPC (entry.pc + 4) = after.setPC row.finish.word.toBitVec at retirement
  change RV.Same next (after.setPC (entry.pc + 4)) at same
  rw [retirement] at same
  have step := (Delegation.Caller.Proofs.rv_source_call source).2 (before.setPC entry.pc) rfl rfl
  rw [family] at step
  exact ⟨next, step.trans called, same⟩

end Airbender.UnifiedReduced.Caller.Proofs
