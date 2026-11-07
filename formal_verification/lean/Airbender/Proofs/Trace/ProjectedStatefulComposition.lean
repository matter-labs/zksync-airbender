import Airbender.Proofs.Trace.StatefulComposition

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

set_option backward.isDefEq.respectTransparency false in
/-- Native row composition after whole-address projection. Full native matching
    still supplies row order and PCs; only actual Sail transfers are filtered. -/
theorem compose_projected_rows_run {Kind Family : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime] {trace : Data p Kind}
    {projection : SailRV32.instruction → Option (DecoderData Family)}
    {clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)}
    {program : List (ProgramEntry Family)} {initial : State} {cells : List Cell}
    (keep : Nat → Bool)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (step : ∀ row ∈ trace.rows, ∀ {before after : State} {events : List MemoryAccess},
      (∀ event ∈ events, event ∈ trace.nativeEvents) →
      SailHistory cells (events.filter fun event => keep event.2.1) initial before →
      SailHistory cells ((rowEvents trace.memoryEpoch row).reverse.filter fun event => keep event.2.1) before after →
      StepWith projection clauseFor program (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec))
    (rows : List (Row p Kind)) (terminal : PCState.State p) {after : State}
    (members : ∀ row ∈ rows, row ∈ trace.rows)
    (native : ∀ event ∈ rows.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents)
    (chain : ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (history : SailHistory cells
      ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
        fun event => keep event.2.1) initial after) :
    Relation.ReflTransGen (StepWith projection clauseFor program) initial (match rows with
      | [] => after
      | _ :: _ => retiredState after terminal.word.toBitVec) := by
  induction rows generalizing terminal after with
  | nil => cases history; exact .refl
  | cons row rest ih =>
    have split : SailHistory cells
        (((rowEvents trace.memoryEpoch row).reverse ++
          rest.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse)).filter
          (fun event => keep event.2.1)) initial after := history
    rw [List.filter_append] at split
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
