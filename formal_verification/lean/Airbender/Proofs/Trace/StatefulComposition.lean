import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Sail.DecoderFrame

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Actual original decoding replays through PC bookkeeping: the unchanged
    source frame theorem only needs the misa image, which retirement preserves. -/
theorem entry_source_retired_state_run {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {entry : ProgramEntry Kind} {before : State}
    (source : entry.SourceWith before projection) (pc : BitVec 32) :
    entry.SourceWith (retiredState before pc) projection :=
  ⟨cell_read_PC (.ram entry.pc) (cell_read_nextPC (.ram entry.pc) source.bytes pc) pc,
    (Reference.Sail.decoded_misa_frame _ source.decoded).2 _
      (by simp [retiredState,Std.ExtDHashMap.get?_insert]),source.fields⟩

/-- Remove bookkeeping at an actual matching PC using real stateful decoding.
    No pure-decoder certificate or per-state replay premise is supplied. -/
theorem step_of_rebased_run {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)}
    {program : List (ProgramEntry Kind)} {before after : State} {pc : BitVec 32}
    (read : run (SailRV32.Functions.get_arch_pc ()) before = .ok pc before)
    (step : StepWith projection clauseFor program (retiredState before pc) after) :
    StepWith projection clauseFor program before after := by
  obtain ⟨entry,present,source,fetched,clause,chosen,normal⟩ := step
  have same : pc = entry.pc :=
    (EStateM.Result.ok.inj ((retired_state_pc before pc).symm.trans fetched)).1
  refine ⟨entry,present,⟨read_word_frame (before := retiredState before pc) (after := before)
    rfl source.bytes,?_,source.fields⟩,same ▸ read,clause,chosen,?_⟩
  · exact (Reference.Sail.decoded_misa_frame _ source.decoded).2 before
      (by simp [retiredState,Std.ExtDHashMap.get?_insert])
  · rw [← normal_step_rebased read clause]
    exact normal

set_option backward.isDefEq.respectTransparency false in
/-- Shared composition for any native family. Per-row rules prove actual Sail
    steps from derived native reads; matching supplies their order and PCs. -/
theorem compose_native_rows_run {Kind Family : Type} [CircuitLayout Kind]
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
        (step_of_rebased_run (by rw [first]; exact pc) checked)
    | cons old rest =>
      exact (ih row.start (fun old present => members old (List.mem_cons_of_mem _ present))
        restNative linked past).tail checked

end Airbender.Trace.Proofs
