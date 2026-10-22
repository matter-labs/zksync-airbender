import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.Execution
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.Trace.RowHistory
import Airbender.Proofs.Sail.DecoderFrame
import Airbender.Proofs.Trace.Terminal
import Mathlib.Data.List.Chain

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

private theorem path_edge_chain {α : Type} {path : List α} {first last : α}
    (head : path.head? = some first) (endPoint : path.getLast? = some last) :
    ((first, first) :: path.zip path.tail ++ [(last, last)]).IsChain
      (fun a b => a.2 = b.1) := by
  induction path generalizing first with
  | nil => simp at head
  | cons a rest ih =>
    have same : a = first := by simpa using head
    subst first
    cases rest with
    | nil =>
      have same : a = last := by simpa using endPoint
      subst last
      simp
    | cons b rest =>
      have tail := ih (first := b) rfl (by simpa using endPoint)
      cases rest with
      | nil => simpa using tail
      | cons c rest =>
        simp only [List.tail_cons, List.zip_cons_cons, List.cons_append,
          List.isChain_cons_cons] at tail ⊢
        exact ⟨trivial, tail⟩

/-- The sorted native rows connect both public endpoints and every adjacent
    instruction boundary. This is derived from the complete state path. -/
theorem ordered_row_boundaries {Kind : Type} [CircuitLayout Kind] [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    [ClockLaws Kind p] (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {rows : List (Row p Kind)} (permutation : rows.Perm trace.rows)
    (ordered : rows.Pairwise (fun a b => rowClock b < rowClock a)) :
    ((trace.terminal, trace.terminal) ::
      rows.map (fun row => (row.start, row.finish)) ++ [(trace.initial, trace.initial)]).IsChain
      (fun a b => a.1 = b.2) := by
  obtain ⟨path, statePath, edges⟩ :=
    ordered_row_state_path hp inverse accepted boundary permutation ordered
  have chain := path_edge_chain statePath.1 statePath.2.1
  have reversed := List.isChain_reverse.mpr chain
  simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
    List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append, edges] using
    reversed.imp (by intro a b equal; exact equal.symm)

/-- Native retirement preserves code and the original decoder configuration. -/
theorem entry_source_retired_state {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {entry : ProgramEntry Kind} {before : State}
    (source : entry.SourceWith before projection) (pc : BitVec 32) :
    entry.SourceWith (retiredState before pc) projection :=
  ⟨cell_read_PC (.ram entry.pc) (cell_read_nextPC (.ram entry.pc) source.bytes pc) pc,
    (decoded_misa_frame _ source.decoded).2 _ (by simp [retiredState, Std.ExtDHashMap.get?_insert]),
    source.fields⟩

/-- Rebasing is proof bookkeeping: original Sail preparation erases nextPC,
    while the public PC, fetched bytes and original decoder remain unchanged. -/
theorem step_of_rebased {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)}
    {program : List (ProgramEntry Kind)} {before after : State} {pc : BitVec 32}
    (read : run (SailRV32.Functions.get_arch_pc ()) before = .ok pc before)
    (step : StepWith projection clauseFor program (retiredState before pc) after) :
    StepWith projection clauseFor program before after := by
  obtain ⟨entry, present, source, fetched, clause, chosen, normal⟩ := step
  have same : pc = entry.pc :=
    (EStateM.Result.ok.inj ((retired_state_pc before pc).symm.trans fetched)).1
  refine ⟨entry, present, ⟨read_word_frame (before := retiredState before pc) (after := before)
    rfl source.bytes, (decoded_misa_frame _ source.decoded).2 _
      (by simp [retiredState, Std.ExtDHashMap.get?_insert]), source.fields⟩,
    same ▸ read, clause, chosen, ?_⟩
  rw [← normal_step_rebased read clause]
  exact normal

/-- A native history whose addresses are all registers preserves every public
    memory byte, including code outside its tracked cell domain. -/
theorem register_history_memory {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (registers : ∀ event ∈ events, ∃ index : BitVec 5,
      event.2.1 = (Cell.register index).addressCode) : after.mem = before.mem := by
  induction history with
  | nil => rfl
  | @cons event rest before middle after past cell member address old written ih =>
    have earlier := ih (fun event present => registers event (List.mem_cons_of_mem _ present))
    obtain ⟨index, code⟩ := registers event List.mem_cons_self
    cases cell with
    | register rd =>
      obtain ⟨result, execution, memory⟩ := gpr_write_memory rd (memoryWord event.2.2.2) middle
      have same := (EStateM.Result.ok.inj (execution.symm.trans written)).2
      subst result
      exact memory.trans earlier
    | ram pc =>
      have impossible := address.trans code
      change Nat.pair 1 _ = Nat.pair 0 _ at impossible
      have different := (Nat.pair_eq_pair.mp impossible).1
      omega

set_option backward.isDefEq.respectTransparency false in
/-- Shared composition for any native family. Per-row rules prove actual Sail
    steps from derived native reads; matching supplies their order and PCs. -/
theorem compose_native_rows {Kind Family : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime] {trace : Data p Kind}
    {projection : SailRV32.instruction → Option (DecoderData Family)}
    {clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)}
    {program : List (ProgramEntry Family)} {initial : State} {cells : List Cell}
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (step : ∀ row ∈ trace.rows, ∀ {before after : State} {events : List MemoryAccess},
      (∀ event ∈ events, event ∈ trace.nativeEvents) →
      SailHistory cells events initial before →
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after →
      StepWith projection clauseFor program (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec))
    (rows : List (Row p Kind)) (terminal : PCState.State p) {after : State}
    (members : ∀ row ∈ rows, row ∈ trace.rows)
    (native : ∀ event ∈ rows.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents)
    (chain : ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (history : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after) :
    Relation.ReflTransGen (StepWith projection clauseFor program) initial (match rows with
      | [] => after
      | _ :: _ => retiredState after terminal.word.toBitVec) := by
  induction rows generalizing terminal after with
  | nil => cases history; exact .refl
  | cons row rest ih =>
    have split : SailHistory cells
        ((rowEvents trace.memoryEpoch row).reverse ++
          rest.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse)) initial after := history
    obtain ⟨middle, past, current⟩ := sail_history_append.mp split
    have linked : terminal = row.finish ∧
        ((row.start, row.start) :: rest.map (fun row => (row.start, row.finish)) ++
          [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2) := by
      cases rest <;> simpa only [List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, List.isChain_cons_cons] using chain
    rcases linked with ⟨rfl, linked⟩
    have restNative : ∀ event ∈ rest.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
        event ∈ trace.nativeEvents := fun event present => native event
      (by simpa only [List.flatMap_cons, List.mem_append] using Or.inr present)
    have checked := step row (members row List.mem_cons_self) restNative past current
    cases rest with
    | nil =>
      have first : row.start = trace.initial := by simpa using linked
      cases past
      exact Relation.ReflTransGen.single
        (step_of_rebased (by rw [first]; exact pc) checked)
    | cons old rest =>
      exact (ih row.start (fun old present => members old (List.mem_cons_of_mem _ present))
        restNative linked past).tail checked

set_option backward.isDefEq.respectTransparency false in
/-- Shared finalization of an already composed native trace. Sail retirement
    preserves its realized cells and exposes the native terminal PC/last writes. -/
theorem native_trace_postconditions {Kind Family : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime] [ClockLaws Kind p]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : Data p Kind} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial nativeAfter : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory) (distinct : cells.Nodup)
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
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial nativeAfter)
    (matched : SailStateMatches cells history nativeAfter)
    (execution : Relation.ReflTransGen (StepWith projection clauseFor program) initial
      (match rows with | [] => nativeAfter | _ :: _ => retiredState nativeAfter trace.terminal.word.toBitVec)) :
    ∃ after, Relation.ReflTransGen (StepWith projection clauseFor program) initial after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
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
  exact ⟨final, execution, pc, terminal_sail_reads hp inverse accepted boundary image distinct consistent realized⟩

end Airbender.Trace.Proofs
