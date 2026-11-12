module
public import Proven.UnifiedReduced.RVCaller.CallerCycles
public import Proven.Blake2G.RVNativeCall
public import Proven.Trace.RVPooledRow

@[expose] public section
namespace Airbender.UnifiedReduced.Caller.Proofs
set_option warningAsError true
open Trace Trace.Proofs Arithmetic

/-- A fetched native G caller takes one actual RV step from its cut in the shared history. -/
theorem rv_g_caller_cycle
    {data : RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry}
    {initial before after : RV.State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program)
    (inputs : RVMixedMemoryInputs data program initial ca oa cells)
    (requests : RVRequestBinding data initial)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.callers)
    {entry : Delegation.Caller.RVProgramEntry}
    (query : row.decoderQuery = Delegation.Caller.rvQuery entry)
    (family : entry.data.family = .blakeG) (source : Delegation.Caller.RVSource before entry)
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
  change kind = .blakeG at selected
  subst kind
  have holds := accepted.workerConstraints _ present
  rw [inputs.tables] at holds
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2G.clockConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) at holds
  have ports : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w)) := by
    intro port included
    obtain ⟨cell, _, address, read, written⟩ := observations port included
    exact ⟨cell, address, by simpa only [readToken, MemoryToken.word, memoryWord] using read,
      by simpa only [Delegation.Row.writeToken, MemoryToken.word, memoryWord] using written⟩
  have words := (rv_mixed_memory_effects accepted inputs).words
  have reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).ports,
      (readToken w port).word.Bounded := by
    intro port included
    exact (words _ (rv_mixed_worker_member present included)).1
  have active := accepted.workerActive _ present
  change w Blake2G.Variables.execute = 1 at active
  obtain ⟨next, called, same⟩ := Blake2G.Proofs.rv_native_g_call holds active reads ports history grouped
    inputs.aligned entry.pc
  have executed : RV.exec (before.setPC entry.pc) (.delegate .blakeG) = some next := by
    simpa only [RV.calls, RV.exec, Option.bind_some, Option.bind_fun_some] using called
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
  exact ⟨next, step.trans executed, same⟩

end Airbender.UnifiedReduced.Caller.Proofs
