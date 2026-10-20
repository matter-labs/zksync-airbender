import Slop.Trace.CompositionCore
import Slop.Trace.RowContext

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false in
theorem compose_native_rows_at {Kind Family : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime] {trace : Data p Kind}
    {projection : SailRV32.instruction → Option (DecoderData Family)}
    {clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)}
    {program : List (ProgramEntry Family)} {initial : State} {cells : List Cell}
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (step : ∀ row ∈ trace.rows, ∀ {before after : State} {events : List MemoryAccess},
      RowPosition trace initial cells row (retiredState before row.start.word.toBitVec) →
      (∀ event ∈ events, event ∈ trace.nativeEvents) →
      SailHistory cells events initial before →
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after →
      StepWith projection clauseFor program (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec))
    (rows newer : List (Row p Kind)) (terminal : PCState.State p) {after : State}
    (permutation : (newer ++ rows).Perm trace.rows)
    (ordered : (newer ++ rows).Pairwise (fun a b => b.clock < a.clock))
    (native : ∀ event ∈ rows.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents)
    (chain : ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (history : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after) :
    Relation.ReflTransGen (StepWith projection clauseFor program) initial (match rows with
      | [] => after
      | _ :: _ => retiredState after terminal.word.toBitVec) := by
  induction rows generalizing newer terminal after with
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
    have position : RowPosition trace initial cells row (retiredState middle row.start.word.toBitVec) := by
      refine ⟨newer, rest, middle, permutation, ordered, ?_, rfl⟩
      simpa only [List.map_flatMap, row_write_values] using SailHistory.writes past
    have member : row ∈ trace.rows := permutation.mem_iff.mp (by simp)
    have checked := step row member position restNative past current
    cases rest with
    | nil =>
      have first : row.start = trace.initial := by simpa using linked
      cases past
      exact Relation.ReflTransGen.single
        (step_of_rebased (by rw [first]; exact pc) checked)
    | cons old rest =>
      have rearranged : (newer ++ [row]) ++ old :: rest = newer ++ row :: old :: rest := by simp
      exact (ih (newer ++ [row]) row.start (rearranged.symm ▸ permutation)
        (rearranged.symm ▸ ordered) restNative linked past).tail checked

end Airbender.Trace.Proofs
