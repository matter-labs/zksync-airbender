import Airbender.Proofs.Trace.TransferTerminal
import Mathlib.Data.List.Perm.Subperm

namespace Airbender.Trace.Proofs.Transfer
set_option warningAsError true
set_option maxRecDepth 16384

def beforeSteps (data : Data p) (cutoff : Nat) :=
  data.steps.filter fun edge => decide ((timeOfPair edge.2.time).value ≤ cutoff)

def afterSteps (data : Data p) (cutoff : Nat) :=
  data.steps.filter fun edge => !decide ((timeOfPair edge.2.time).value ≤ cutoff)

theorem partition_steps (data : Data p) (cutoff : Nat) :
    (beforeSteps data cutoff ++ afterSteps data cutoff).Perm data.steps :=
  List.filter_append_perm _ _

theorem prefix_reads_covered {data : Data p} (facts : Facts data) (cutoff : Nat) :
    List.Subperm ((beforeSteps data cutoff).map Prod.fst)
      (data.initial ++ (beforeSteps data cutoff).map Prod.snd) := by
  apply List.subperm_iff_count.mpr
  intro token
  by_cases missing : token ∉ (beforeSteps data cutoff).map Prod.fst
  · rw [List.count_eq_zero_of_not_mem missing]
    exact Nat.zero_le _
  · have present := Classical.not_not.mp missing
    obtain ⟨edge, member, same⟩ := List.mem_map.mp present
    have earlyMembership := List.mem_filter.mp member
    have bound : (timeOfPair edge.2.time).value ≤ cutoff := of_decide_eq_true earlyMembership.2
    have ordered := facts.order edge earlyMembership.1
    have absent : token ∉ (afterSteps data cutoff).map Prod.snd := by
      intro included
      obtain ⟨later, laterMember, equal⟩ := List.mem_map.mp included
      have suffix := List.mem_filter.mp laterMember
      have late : cutoff < (timeOfPair later.2.time).value := by
        have rejected : ¬ (timeOfPair later.2.time).value ≤ cutoff := by
          intro le
          have remaining : (!decide ((timeOfPair later.2.time).value ≤ cutoff)) = true := suffix.2
          rw [decide_eq_true le] at remaining
          cases remaining
        omega
      have time := congrArg (fun value : MemoryToken p => (timeOfPair value.time).value)
        (equal.trans same.symm)
      omega
    have matching := facts.matching.count_eq token
    have writes := ((partition_steps data cutoff).map Prod.snd).count_eq token
    have reads := ((partition_steps data cutoff).map Prod.fst).count_eq token
    simp only [List.map_append, List.count_append] at writes reads matching ⊢
    rw [List.count_eq_zero_of_not_mem absent] at writes
    omega

theorem split_at {data : Data p} (facts : Facts data) (cutoff : Nat) :
    ∃ middle : List (MemoryToken p),
      Facts ⟨data.initial, middle, beforeSteps data cutoff⟩ ∧
      Facts ⟨middle, data.terminal, afterSteps data cutoff⟩ := by
  obtain ⟨arranged, permutation, inclusion⟩ := List.subperm_iff.mp (prefix_reads_covered facts cutoff)
  obtain ⟨middle, boundary⟩ := inclusion.exists_perm_append
  have leftMatching := (permutation.symm.trans boundary).trans (List.perm_append_comm)
  have suffix : (middle ++ (afterSteps data cutoff).map Prod.snd).Perm
      (data.terminal ++ (afterSteps data cutoff).map Prod.fst) := by
    apply List.perm_iff_count.mpr
    intro token
    have first := leftMatching.count_eq token
    have matching := facts.matching.count_eq token
    have writes := ((partition_steps data cutoff).map Prod.snd).count_eq token
    have reads := ((partition_steps data cutoff).map Prod.fst).count_eq token
    simp only [List.map_append, List.count_append] at first matching writes reads ⊢
    omega
  refine ⟨middle, ⟨leftMatching, ?_, ?_⟩, ⟨suffix, ?_, ?_⟩⟩
  all_goals intro edge member
  · exact facts.addresses edge (List.mem_of_mem_filter member)
  · exact facts.order edge (List.mem_of_mem_filter member)
  · exact facts.addresses edge (List.mem_of_mem_filter member)
  · exact facts.order edge (List.mem_of_mem_filter member)

theorem split_sail_state {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : Inputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) (cutoff : Nat) :
    ∃ (middle : List (MemoryToken p)) (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
      Facts ⟨data.initial, middle, beforeSteps data cutoff⟩ ∧
      Facts ⟨middle, data.terminal, afterSteps data cutoff⟩ ∧
      events.Perm ((beforeSteps data cutoff).map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      SailHistory cells events before after ∧
      ∀ token ∈ middle, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after := by
  obtain ⟨middle, earlier, later⟩ := split_at facts cutoff
  have initialized : Inputs ⟨data.initial, middle, beforeSteps data cutoff⟩ before cells :=
    ⟨inputs.initialization, inputs.distinct⟩
  have prefixZero : ∀ edge ∈ beforeSteps data cutoff, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0 := fun edge member => zero edge (List.mem_of_mem_filter member)
  obtain ⟨history, events, after, matched, native, ordered, realized, state⟩ :=
    native_sail_history earlier initialized aligned prefixZero
  exact ⟨middle, events, after, earlier, later, native, ordered, realized,
    terminal_sail_reads earlier initialized matched state⟩

end Airbender.Trace.Proofs.Transfer
