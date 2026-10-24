import Tests.PathGConsumedMessage.Native
import Tests.PathGLoop

namespace Tests.PathGConsumedMessage
open Airbender Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
open Airbender.UnifiedReduced.Caller Airbender.UnifiedReduced.Caller.Proofs
open Tests.PathGLoopProgram
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

private theorem events_end :
    (data.mixedSteps.map transferEvent).all (fun event => decide (event.1 ≤ 916)) = true := by
  decide +kernel

private theorem prefix_only_registers :
    (data.mixedSteps.map transferEvent).all (fun event =>
      decide (event.1 ≤ 28 → event.2.1 ≤ (Cell.register 31).addressCode)) = true := by
  decide +kernel

private theorem ram_above_registers (address : BitVec 32)
    (member : Cell.ram address ∈ PathGLoopNative.cells) :
    (Cell.register 31).addressCode < (Cell.ram address).addressCode := by
  simp only [PathGLoopNative.cells, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ((⟨index, _, same⟩ | ⟨index, _, same⟩) | ⟨index, _, same⟩) | same
  · cases same
  · cases same
    fin_cases index <;> decide +kernel
  · cases same
    fin_cases index <;> decide +kernel
  · cases same
    decide +kernel

private theorem prefix_pointer_touched (index : Fin 2) :
    (data.mixedSteps.map transferEvent).any (fun event =>
      decide (event.1 ≤ 28 ∧ event.2.1 =
        (Cell.register (if index.val = 0 then 10 else 11)).addressCode)) = true := by
  fin_cases index <;> decide +kernel

private theorem prefix_pointer_values (index : Fin 2) :
    (data.mixedSteps.map transferEvent).all (fun event =>
      decide (event.1 ≤ 28 → event.2.1 =
        (Cell.register (if index.val = 0 then 10 else 11)).addressCode →
        memoryWord event.2.2.2 = (if index.val = 0 then stateAddress else messageAddress))) = true := by
  fin_cases index <;> decide +kernel

private theorem prefix_pointer {events : List MemoryAccess} {first : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (past : SailHistory PathGLoopNative.cells
      (events.filter fun event => decide (event.1 ≤ 28)) before first) (index : Fin 2) :
    (Cell.register (if index.val = 0 then 10 else 11)).read first =
      .ok (if index.val = 0 then stateAddress else messageAddress) first := by
  apply PathGLoop.history_uniform_value past PathGLoopNative.cells_aligned _ trivial
    (by fin_cases index <;> decide) _
  · obtain ⟨event, member, chosen⟩ := List.any_eq_true.mp (prefix_pointer_touched index)
    have facts := of_decide_eq_true chosen
    exact ⟨event, List.mem_filter.mpr ⟨permutation.mem_iff.mpr member,
      decide_eq_true facts.1⟩, facts.2⟩
  · intro event member address
    obtain ⟨included, chosen⟩ := List.mem_filter.mp member
    have facts := of_decide_eq_true (List.all_eq_true.mp (prefix_pointer_values index) event
      (permutation.mem_iff.mp included))
    exact facts (of_decide_eq_true chosen) address

private theorem prefix_ram_zero {events : List MemoryAccess} {first : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (past : SailHistory PathGLoopNative.cells
      (events.filter fun event => decide (event.1 ≤ 28)) before first)
    (address : BitVec 32) (member : Cell.ram address ∈ PathGLoopNative.cells) :
    (Cell.ram address).read first = .ok 0 first := by
  apply history_cell_frame past PathGLoopNative.cells_aligned (.ram address)
    (PathGLoopNative.cells_aligned _ member) ?_ (ram_zero address member)
  intro event included same
  obtain ⟨included, chosen⟩ := List.mem_filter.mp included
  have bound := of_decide_eq_true (List.all_eq_true.mp prefix_only_registers event
    (permutation.mem_iff.mp included))
  have low := bound (of_decide_eq_true chosen)
  have high := ram_above_registers address member
  omega

private theorem suffix_output_touched :
    (data.mixedSteps.map transferEvent).any (fun event =>
      decide (909 < event.1 ∧ event.1 ≤ 916 ∧
        event.2.1 = (Cell.ram (stateAddress + 12)).addressCode)) = true := by
  decide +kernel

private theorem suffix_output_values :
    (data.mixedSteps.map transferEvent).all (fun event =>
      decide (909 < event.1 → event.2.1 = (Cell.ram (stateAddress + 12)).addressCode →
        memoryWord event.2.2.2 = 119)) = true := by
  decide +kernel

private theorem final_output {events : List MemoryAccess} {after : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory PathGLoopNative.cells events before after) :
    (Cell.ram (stateAddress + 12)).read after = .ok 119 after := by
  have noLater : (events.filter fun event => decide (916 < event.1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member chosen
    have bound := of_decide_eq_true (List.all_eq_true.mp events_end event
      (permutation.mem_iff.mp member))
    have later := of_decide_eq_true chosen
    omega
  obtain ⟨first, last, _, _, current, future⟩ := history_window order history (by decide : 909 ≤ 916)
  have lastValue : (Cell.ram (stateAddress + 12)).read last = .ok 119 last := by
    apply PathGLoop.history_uniform_value current PathGLoopNative.cells_aligned _
      (PathGLoopNative.cells_aligned _ (by decide +kernel)) (by decide) 119
    · obtain ⟨event, member, chosen⟩ := List.any_eq_true.mp suffix_output_touched
      have facts := of_decide_eq_true chosen
      exact ⟨event, List.mem_filter.mpr ⟨permutation.mem_iff.mpr member,
        decide_eq_true ⟨facts.1, facts.2.1⟩⟩, facts.2.2⟩
    · intro event member address
      obtain ⟨included, chosen⟩ := List.mem_filter.mp member
      have facts := of_decide_eq_true (List.all_eq_true.mp suffix_output_values event
        (permutation.mem_iff.mp included))
      exact facts (of_decide_eq_true chosen).1 address
  rw [noLater] at future
  cases future
  exact lastValue

private def zeroWords : Vector Word 16 := Vector.replicate 16 ⟨0, 0⟩


private theorem zero_run : Blake2G.WorkVector.run true zeroWords zeroWords =
    Vector.replicate 16 0 := by decide +kernel

/-- Every chronological native history has output119 in lane3, whereas the
independent56-call G computation on its zero input/message has output0. This
contradiction uses output computation and never uses messageUnchanged. -/
theorem no_algorithm {events : List MemoryAccess}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1)) :
    ¬ ∃ first last : State,
      SailHistory PathGLoopNative.cells (events.filter fun event => decide (event.1 ≤ 28)) before first ∧
      SailHistory PathGLoopNative.cells
        (events.filter fun event => decide (28 < event.1 ∧ event.1 ≤ 916)) first last ∧
      PathSpanAlgorithmResult (.blakeG true) first last := by
  rintro ⟨first, last, past, current, statePointer, messagePointer, input, message, output, mapping, algorithm⟩
  have pointerState : statePointer = stateAddress :=
    (EStateM.Result.ok.inj (mapping.pointers.1.symm.trans (prefix_pointer permutation past 0))).1
  have pointerMessage : messagePointer = messageAddress :=
    (EStateM.Result.ok.inj (mapping.pointers.2.symm.trans (prefix_pointer permutation past 1))).1
  have inputsZero : input = zeroWords := by
    apply Vector.ext
    intro j bound
    let index : Fin 16 := ⟨j, bound⟩
    suffices wordZero : input[index] = ⟨0, 0⟩ by
      simpa only [zeroWords, Vector.getElem_replicate, Fin.getElem_fin] using wordZero
    apply Word.eq_zero_of_bounded (mapping.inputWords index).1
    have zero := prefix_ram_zero permutation past
      (stateAddress + BitVec.ofNat 32 (4 * index.val)) (by
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩)
    have actual := (mapping.inputWords index).2
    simp only [pointerState, Nat.zero_add] at actual
    exact (EStateM.Result.ok.inj (actual.symm.trans zero)).1
  have messageZero : message = zeroWords := by
    apply Vector.ext
    intro j bound
    let index : Fin 16 := ⟨j, bound⟩
    suffices wordZero : message[index] = ⟨0, 0⟩ by
      simpa only [zeroWords, Vector.getElem_replicate, Fin.getElem_fin] using wordZero
    apply Word.eq_zero_of_bounded (mapping.messageWords index).1
    have zero := prefix_ram_zero permutation past
      (messageAddress + BitVec.ofNat 32 (4 * index.val)) (by
        apply List.mem_append_left
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩)
    have actual := (mapping.messageWords index).2
    simp only [pointerMessage, Nat.zero_add] at actual
    exact (EStateM.Result.ok.inj (actual.symm.trans zero)).1
  rw [inputsZero, messageZero, zero_run] at algorithm
  have expected : output[3].value = 0 := by
    simpa only [Vector.getElem_map, Vector.getElem_replicate]
      using congrArg (fun words : Vector Nat 16 => words[3]) algorithm
  have allEvents : (events.filter fun event => decide (event.1 ≤ 916)) = events := by
    apply List.filter_eq_self.mpr
    intro event member
    exact List.all_eq_true.mp events_end event (permutation.mem_iff.mp member)
  have full := history_prefix_of_window order (by decide : 28 ≤ 916) past current
  rw [allEvents] at full
  have actual := (mapping.outputWords (3 : Fin 16)).2
  simp only [pointerState] at actual
  have nonzero := final_output permutation order full
  have encoded : output[3].toBitVec = 119 := (EStateM.Result.ok.inj (actual.symm.trans nonzero)).1
  have bounded : output[3].Bounded := by
    simpa [Fin.getElem_fin] using (mapping.outputWords (3 : Fin 16)).1
  have value := congrArg BitVec.toNat encoded
  rw [Word.toBitVec_toNat bounded, expected] at value
  exact (by decide : (0 : Nat) ≠ (119 : BitVec 32).toNat) value

/-- The counterexample is inhabited by an initialized history of the actual
accepted228 CPU rows and56 G rows, with the changed state output read back. -/
theorem native_execution : ∃ events : List MemoryAccess, ∃ after : State,
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    SailHistory PathGLoopNative.cells events before after ∧
    (Cell.ram (stateAddress + 12)).read after = .ok 119 after := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, after, permutation, order, history, _⟩ := effects.execution
  exact ⟨events, after, permutation, order, history, final_output permutation order history⟩

end Tests.PathGConsumedMessage
