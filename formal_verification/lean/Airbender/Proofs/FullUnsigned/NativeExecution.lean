import Airbender.Proofs.FullUnsigned.NativeComposition
import Airbender.Proofs.FullUnsigned.EventInterval

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The actual complete full native path realizes the combined reference relation.
This physical-history stage keeps worker input contracts and ROM interpretation
separate. It assumes no instruction or worker execution result. -/
theorem unrolled_full_physical_execution
    {initial finalState : State}
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle) (splitBundles : List Keccak.Split.Bundle) {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (closure : VerifierBoundary.BootClosure trace.initial
      (trace.rows.map Row.start) (trace.rows.map Row.finish))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (fixedEquations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached Keccak.Split.Native.Proofs.fixedSetup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {cells : List Cell} {physicalImage : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some physicalImage)
    (wordSetup : trace.rom.wordMemory = ROM.table cells physicalImage)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (profile : PooledPublicInputs initial cells
      (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text))
    {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    (inputs : Transfer.NativeInputs (unrolledFullMemoryData trace workers splitWorkers) initial cells)
    (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (workerFamilies : ∀ worker ∈ workers.rows, FullUnsigned.standardCall worker.family)
    (bounds : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      edge.1.word.Bounded ∧ edge.2.word.Bounded)
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (commands : ∀ worker ∈ workers.rows, worker.family = .bigint →
      ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (splitInputs : ∀ row ∈ trace.rows, ∀ worker ∈ splitWorkers.rows,
      worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment →
      ∀ before, SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before →
        ∃ index : Fin 361, Keccak.Split.ArgumentsAt index.val before)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (terminal : ∀ token ∈ trace.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read finalState = .ok token.word.toBitVec finalState) :
    FullUnsigned.Realizes stream (FullUnsigned.Program.ofText initial text bundles splitBundles)
      trace initial cells := by
  let program := FullUnsigned.Program.ofText initial text bundles splitBundles
  obtain ⟨path, head, endPoint, edges, _⟩ := state_path_checks (by decide) (by decide)
    accepted.cpuEquations accepted.states initialClock
    initialAligned
  let point (state : PCState.State babyBearModulus) :=
    (((timeOfPair state.timestamp).value, state.word.toBitVec),
      AddSub.Modular.External.Caller.countAt trace (timeOfPair state.timestamp).value)
  have initialEmpty : (events.filter fun event => decide
      (event.1 ≤ (timeOfPair trace.initial.timestamp).value)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member chosen
    have bound := (unrolled_full_event_interval accepted equations active initialClock initialAligned
      (permutation.mem_iff.mp member)).1
    have selected := of_decide_eq_true chosen
    omega
  have terminalAll : (events.filter fun event => decide
      (event.1 ≤ (timeOfPair trace.terminal.timestamp).value)) = events := by
    apply List.filter_eq_self.mpr
    intro event member
    exact decide_eq_true (unrolled_full_event_interval accepted equations active initialClock initialAligned
      (permutation.mem_iff.mp member)).2
  have past : CutState cells events initial (point trace.initial).1.1 initial := by
    unfold CutState
    rw [initialEmpty]
    exact .nil _
  have finish : CutState cells events initial (point trace.terminal).1.1 finalState := by
    unfold CutState
    rw [terminalAll]
    exact history
  have transitions : ∀ edge ∈ (path.map point).zip (path.map point).tail, ∃ one two,
      CutState cells events initial edge.1.1.1 one ∧
      CutState cells events initial edge.2.1.1 two ∧
      FullUnsigned.Step stream program
        (retiredState one edge.1.1.2, edge.1.2)
        (retiredState two edge.2.1.2, edge.2.2) ∧
      (run (SailRV32.Functions.get_arch_pc ()) one = .ok edge.1.1.2 one →
        FullUnsigned.Step stream program (one, edge.1.2)
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
    exact unrolled_full_cycle_transition bundles splitBundles setup lookup accepted excluded initialPC closure
      equations fixedEquations active initialClock initialAligned image wordSetup subwordSetup aligned profile
      permutation ordered history readonly facts inputs workerSetup workerFamilies bounds ram commands controls
      splitInputs stream ports present
  have first : (path.map point).head? = some (point trace.initial) := by
    simpa using congrArg (Option.map point) head
  have last : (path.map point).getLast? = some (point trace.terminal) := by
    simpa using congrArg (Option.map point) endPoint
  obtain ⟨after, execution, view⟩ :=
    compose_cuts_with_count first last pc past finish transitions
  refine ⟨after, ?_, ?_, ?_⟩
  · simpa only [point, AddSub.Modular.External.Caller.countAt, unrolled_full_initial_count accepted initialClock initialAligned,
      unrolled_full_terminal_count accepted initialClock initialAligned] using execution
  · rcases view with ⟨rfl, same⟩ | rfl
    · have samePC := congrArg (fun position => position.1.2) same
      change trace.initial.word.toBitVec = trace.terminal.word.toBitVec at samePC
      rw [← samePC]
      exact sail_history_pc_read history pc
    · exact retired_state_pc _ _
  · intro token member
    obtain ⟨cell, included, address, read⟩ := terminal token member
    rcases view with ⟨rfl, _⟩ | rfl
    · exact ⟨cell, included, address, read⟩
    · exact ⟨cell, included, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩


end Airbender.Compiler.MachineTargets.Proofs
