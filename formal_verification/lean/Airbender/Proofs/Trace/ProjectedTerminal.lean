import Airbender.Proofs.Trace.ProjectedComposition

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Native matching roots every retained terminal address in the actual public
    Sail image. Its last value comes from the complete, unfiltered Clean history. -/
theorem projected_terminal_reads {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before after : State} {cells : List Cell} (keep : Nat → Bool)
    (image : initialImage before cells = some (trace.initialMemory.filter fun token => keep token.address))
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup)
    {history : TimestampSortedMemoryAccessList} (consistent : MemoryHistory trace history)
    (realized : SailStateMatches cells history after) :
    ∀ sink ∈ trace.terminalMemory, keep sink.address = true →
      ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord sink.value) after := by
  intro sink member selected
  have keys := boundary_keys MemoryToken.address (memory_steps_matched accepted) memory_steps_address
  obtain ⟨source, present, address⟩ := List.mem_map.mp
    (keys.mem_iff.mpr (List.mem_map.mpr ⟨sink, member, rfl⟩))
  have retained : source ∈ trace.initialMemory.filter (fun token => keep token.address) := List.mem_filter.mpr ⟨present, by rw [address]; exact selected⟩
  obtain ⟨cell, cellMember, _, _, same⟩ := image_sources image source retained
  have code : source.address = cell.addressCode := congrArg MemoryToken.address same
  refine ⟨cell, cellMember, code.symm.trans address, ?_⟩
  have read := realized cell cellMember
  have latest := terminal_latest_value hp accepted boundary unique consistent member
  rw [code.symm.trans address, latest] at read
  exact read

set_option backward.isDefEq.respectTransparency false in
/-- Final retirement preserves the projected architectural cells and exposes
    the exact native terminal PC. Full native matching still includes erased tokens. -/
theorem projected_trace_postconditions {Kind Family : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime] [ClockLaws Kind p]
    (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial nativeAfter : State} {cells : List Cell}
    (keep : Nat → Bool)
    (image : initialImage initial cells = some (trace.initialMemory.filter fun token => keep token.address))
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup)
    {projection : SailRV32.instruction → Option (DecoderData Family)}
    {clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)}
    {program : List (ProgramEntry Family)}
    (initialRead : run (SailRV32.Functions.get_arch_pc ()) initial =
      .ok trace.initial.word.toBitVec initial)
    {history : TimestampSortedMemoryAccessList} (consistent : MemoryHistory trace history)
    {rows : List (Row p Kind)}
    (chain : ((trace.terminal, trace.terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (nativeHistory : SailHistory cells
      ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
        fun event => keep event.2.1) initial nativeAfter)
    (matched : SailStateMatches cells history nativeAfter)
    (execution : Relation.ReflTransGen (StepWith projection clauseFor program) initial
      (match rows with | [] => nativeAfter | _ :: _ => retiredState nativeAfter trace.terminal.word.toBitVec)) :
    ∃ after, Relation.ReflTransGen (StepWith projection clauseFor program) initial after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, keep sink.address = true →
        ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord sink.value) after := by
  let final := match rows with
    | [] => nativeAfter
    | _ :: _ => retiredState nativeAfter trace.terminal.word.toBitVec
  have pc : run (SailRV32.Functions.get_arch_pc ()) final = .ok trace.terminal.word.toBitVec final := by
    cases rows with
    | nil =>
      have same : trace.terminal = trace.initial := by simpa using chain
      rw [same]
      exact sail_history_pc_read nativeHistory initialRead
    | cons _ _ => exact retired_state_pc nativeAfter trace.terminal.word.toBitVec
  have realized : SailStateMatches cells history final := by
    cases rows with
    | nil => exact matched
    | cons _ _ =>
      exact matches_control
        (matches_control matched .nextPC (.inr rfl) trace.terminal.word.toBitVec)
        .PC (.inl rfl) trace.terminal.word.toBitVec
  exact ⟨final, execution, pc, projected_terminal_reads hp accepted boundary keep image unique consistent realized⟩

end Airbender.Trace.Proofs
