import Airbender.Proofs.FullUnsigned.SupportedSplit
import Airbender.Proofs.FullUnsigned.CallHistory

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Derived split input tokens recover supported arguments at the exact native
caller cut in any matching initialized history. No lane value is assumed. -/
theorem unrolled_full_split_arguments_at_cut
    {initial finalState : State} {text : List (BitVec 32)} {capacity : Nat}
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
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {cells : List Cell}
    (inputs : Transfer.NativeInputs (unrolledFullMemoryData trace workers splitWorkers) initial cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Keccak.Split.Native.Row babyBearModulus) (present : worker ∈ splitWorkers.rows)
    (matched : worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)
    (arguments : Keccak.Split.Native.Proofs.nativeCallArguments splitWorkers.cached worker)
    {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (before : State)
    (givenPast : SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before) :
    ∃ index : Fin 361, Keccak.Split.ArgumentsAt index.val before := by
  obtain ⟨atCall, after, past, localHistory, localEvents, _⟩ :=
    unrolled_full_split_caller_history setup lookup accepted excluded initialPC equations active
      initialClock initialAligned row member family selected worker present matched permutation ordered history
  have same := sail_history_deterministic past givenPast
  subst atCall
  have readable := history_cells_readable givenPast aligned (by
    intro cell included
    obtain ⟨_, _, _, read, _⟩ := Transfer.native_cell_source inputs included
    exact ⟨_, read⟩)
  apply Keccak.Split.Native.Proofs.native_arguments_at_observations splitWorkers.cached worker arguments before
  intro register
  obtain ⟨cell, _, address, read⟩ := Keccak.Split.Native.Proofs.native_register_observation
    splitWorkers.cached worker register localHistory localEvents aligned readable
  exact ⟨cell, address, read⟩

end Airbender.Compiler.MachineTargets.Proofs
