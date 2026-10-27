import Slop.Trace.CompositionCore
import Slop.Trace.ExternalStream
import Human.Trace.NonDeterminism

namespace Airbender.Trace.ExternalStream.Proofs
open Reference.RiscV.Sail Reference.Sail Trace.Proofs

private theorem head_index {Kind : Type} [CircuitLayout Kind] {p : Nat}
    (read : Row p Kind → Bool) (index : Row p Kind → Nat)
    {row : Row p Kind} {rows : List (Row p Kind)}
    (ordered : (row :: rows).Pairwise (fun a b => b.clock < a.clock))
    (equal : index row = ((row :: rows).filter fun earlier =>
      read earlier && decide (earlier.clock < row.clock)).length) :
    index row = (rows.filter read).length := by
  rw [equal]
  simp only [List.filter_cons, lt_self_iff_false, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply List.filter_congr
  intro old member
  simp [(List.pairwise_cons.mp ordered).1 old member]

private theorem remaining_indices {Kind : Type} [CircuitLayout Kind] {p : Nat}
    (read : Row p Kind → Bool) (index : Row p Kind → Nat)
    {row : Row p Kind} {rows : List (Row p Kind)}
    (ordered : (row :: rows).Pairwise (fun a b => b.clock < a.clock))
    (indices : ∀ current ∈ row :: rows, index current =
      ((row :: rows).filter fun earlier => read earlier &&
        decide (earlier.clock < current.clock)).length) :
    ∀ current ∈ rows, index current =
      (rows.filter fun earlier => read earlier && decide (earlier.clock < current.clock)).length := by
  intro current member
  have previous := (List.pairwise_cons.mp ordered).1 current member
  have equal := indices current (List.mem_cons_of_mem row member)
  simpa [List.filter_cons, Nat.not_lt.mpr (Nat.le_of_lt previous)] using equal

def finalState {Kind : Type} [CircuitLayout Kind] {p : Nat}
    (rows : List (Row p Kind)) (after : State) (pc : BitVec 32) : State :=
  match rows with | [] => after | _ :: _ => retiredState after pc


theorem step_of_rebased {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)} {profile : ISAProfile}
    {stream : List (BitVec 32)} {program : List (ProgramEntry Kind)}
    {before after : State} {pc : BitVec 32} {position next : Nat}
    (read : run (SailRV32.Functions.get_arch_pc ()) before = .ok pc before)
    (step : NonDeterminism.StepWith projection profile stream program
      (retiredState before pc, position) (after, next)) :
    NonDeterminism.StepWith projection profile stream program (before, position) (after, next) := by
  obtain ⟨entry, present, source, fetched, original, chosen, normal⟩ := step
  have same : pc = entry.pc :=
    (EStateM.Result.ok.inj ((retired_state_pc before pc).symm.trans fetched)).1
  refine ⟨entry, present, ⟨read_word_frame (before := retiredState before pc) (after := before)
    rfl source.bytes, (decoded_misa_frame _ source.decoded).2 _
      (((ConfigSame.refl before).insert (key := .nextPC) rfl pc).insert (key := .PC) rfl pc).symm, source.fields⟩,
    same ▸ read, original, chosen, ?_⟩
  rw [← normal_step_rebased read original]
  exact normal

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem compose_rows {Kind Family : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    {trace : Data p Kind} (read : Row p Kind → Bool) (index : Row p Kind → Nat)
    {projection : SailRV32.instruction → Option (DecoderData Family)} {profile : ISAProfile}
    {stream : List (BitVec 32)} {program : List (ProgramEntry Family)}
    {initial : State} {cells : List Cell}
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (step : ∀ row ∈ trace.rows, ∀ {before after : State} {events : List MemoryAccess},
      (∀ event ∈ events, event ∈ trace.nativeEvents) →
      SailHistory cells events initial before →
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after →
      NonDeterminism.StepWith projection profile stream program
        (retiredState before row.start.word.toBitVec, index row)
        (retiredState after row.finish.word.toBitVec, index row + if read row then 1 else 0))
    (rows : List (Row p Kind))
    (ordered : rows.Pairwise (fun a b => b.clock < a.clock))
    (indices : ∀ current ∈ rows, index current =
      (rows.filter fun earlier => read earlier && decide (earlier.clock < current.clock)).length)
    (terminal : PCState.State p) {after : State}
    (members : ∀ row ∈ rows, row ∈ trace.rows)
    (native : ∀ event ∈ rows.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents)
    (chain : ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (history : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after) :
    Relation.ReflTransGen (NonDeterminism.StepWith projection profile stream program) (initial, 0)
      (finalState rows after terminal.word.toBitVec,
        (rows.filter read).length) := by
  induction rows generalizing terminal after with
  | nil =>
    cases history
    exact .refl
  | cons row rest ih =>
    have position : (rest.filter read).length = index row :=
      (head_index read index ordered (indices row List.mem_cons_self)).symm
    have restIndices := remaining_indices read index ordered indices
    have restOrdered := (List.pairwise_cons.mp ordered).2
    have count : ((row :: rest).filter read).length =
        (rest.filter read).length + if read row then 1 else 0 := by
      cases selected : read row <;> simp [selected]
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
    have restMembers : ∀ old ∈ rest, old ∈ trace.rows :=
      fun old present => members old (List.mem_cons_of_mem row present)
    have restNative : ∀ event ∈ rest.flatMap (fun row => (rowEvents trace.memoryEpoch row).reverse),
        event ∈ trace.nativeEvents := fun event present => native event
      (by simpa only [List.flatMap_cons, List.mem_append] using Or.inr present)
    have checked := step row (members row List.mem_cons_self) restNative past current
    rw [← position] at checked
    rw [count]
    cases rest with
    | nil =>
      have first : row.start = trace.initial := by simpa using linked
      cases past
      have currentPC : run (SailRV32.Functions.get_arch_pc ()) initial =
          .ok row.start.word.toBitVec initial := by rw [first]; exact pc
      exact Relation.ReflTransGen.single (step_of_rebased currentPC checked)
    | cons old rest =>
      have previous := ih restOrdered restIndices row.start restMembers restNative linked past
      exact previous.tail checked

end Airbender.Trace.ExternalStream.Proofs
