import Airbender.Proofs.UnifiedReduced.StreamROMComposition

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

/-- Compose the actual native path with its exact external-stream positions.
Native caller retirement and the physical code profile remain separate inputs. -/
theorem execution_at_readonly [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial finalState : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (requests : RequestBinding data initial)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial =
      .ok data.machine.initial.word.toBitVec initial)
    (ledger : ExternalBoundary.Requests.Binding data)
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (stream : List (BitVec 32))
    (ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers →
      Stream.OrdinaryCycle stream program data.machine cells events initial finalState row)
    (callers : ∀ row ∈ data.callers,
      FullCallerCycle data initial finalState cells events row)
    (terminal : ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read finalState = .ok token.word.toBitVec finalState) :
    Stream.Realizes stream program data.program data.machine initial cells := by
  obtain ⟨path, head, endPoint, edges, _⟩ := state_path_checks (by decide) (by decide)
    accepted.constraints accepted.states inputs.publicProgram.initialClock
    inputs.publicProgram.initialAligned
  let point (state : PCState.State babyBearModulus) :=
    (((timeOfPair state.timestamp).value, state.word.toBitVec),
      Stream.countAt data.machine (timeOfPair state.timestamp).value)
  have initialEmpty : (events.filter fun event => decide
      (event.1 ≤ (timeOfPair data.machine.initial.timestamp).value)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member chosen
    have bound := (mixed_event_interval accepted inputs.publicProgram requests ledger
      (permutation.mem_iff.mp member)).1
    have selected := of_decide_eq_true chosen
    omega
  have terminalAll : (events.filter fun event => decide
      (event.1 ≤ (timeOfPair data.machine.terminal.timestamp).value)) = events := by
    apply List.filter_eq_self.mpr
    intro event member
    exact decide_eq_true (mixed_event_interval accepted inputs.publicProgram requests ledger
      (permutation.mem_iff.mp member)).2
  have past : CutState cells events initial (point data.machine.initial).1.1 initial := by
    unfold CutState
    rw [initialEmpty]
    exact .nil _
  have finish : CutState cells events initial (point data.machine.terminal).1.1 finalState := by
    unfold CutState
    rw [terminalAll]
    exact history
  have transitions : ∀ edge ∈ (path.map point).zip (path.map point).tail, ∃ one two,
      CutState cells events initial edge.1.1.1 one ∧
      CutState cells events initial edge.2.1.1 two ∧
      Stream.Step stream program data.program
        (retiredState one edge.1.1.2, edge.1.2)
        (retiredState two edge.2.1.2, edge.2.2) ∧
      (run (SailRV32.Functions.get_arch_pc ()) one = .ok edge.1.1.2 one →
        Stream.Step stream program data.program (one, edge.1.2)
          (retiredState two edge.2.1.2, edge.2.2)) := by
    intro edge included
    have mapped : ∀ states : List (PCState.State babyBearModulus),
        (states.map point).zip (states.map point).tail =
          (states.zip states.tail).map (fun edge => (point edge.1, point edge.2)) := by
      intro states
      induction states with
      | nil => rfl
      | cons a rest ih =>
        cases rest with
        | nil => rfl
        | cons b rest =>
          simpa only [List.map_cons, List.tail_cons, List.zip_cons_cons] using
            congrArg (List.cons (point a, point b)) ih
    rw [mapped path] at included
    obtain ⟨native, member, rfl⟩ := List.mem_map.mp included
    obtain ⟨row, present, equal⟩ := List.mem_map.mp (edges.mem_iff.mp member)
    subst native
    exact full_cycle_transition_readonly accepted inputs code unchanged requests order stream ordinary callers present
  have first : (path.map point).head? = some (point data.machine.initial) := by
    simpa using congrArg (Option.map point) head
  have last : (path.map point).getLast? = some (point data.machine.terminal) := by
    simpa using congrArg (Option.map point) endPoint
  obtain ⟨after, execution, view⟩ :=
    compose_cuts_with_count first last pc past finish transitions
  refine ⟨after, ?_, ?_, ?_⟩
  · simpa only [point, Stream.countAt, native_initial_count accepted.toRequestChecks inputs.publicProgram,
      native_terminal_count accepted.toRequestChecks inputs.publicProgram] using execution
  · rcases view with ⟨rfl, same⟩ | rfl
    · have samePC := congrArg (fun position => position.1.2) same
      change data.machine.initial.word.toBitVec = data.machine.terminal.word.toBitVec at samePC
      rw [← samePC]
      exact sail_history_pc_read history pc
    · exact retired_state_pc _ _
  · intro token member
    obtain ⟨cell, included, address, read⟩ := terminal token member
    rcases view with ⟨rfl, _⟩ | rfl
    · exact ⟨cell, included, address, read⟩
    · exact ⟨cell, included, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩

end Airbender.UnifiedReduced.Caller.Stream.Proofs
