import Airbender.Proofs.UnifiedReduced.FullComposition

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

theorem full_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {regions : List RoundRegion} {windows : List HashWindow} {cut : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramComputedPreparedProtocolInputs data initial ca oa cells program regions)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (ledger : ExternalBoundary.Requests.Binding data)
    (scopes : ∀ window ∈ windows, WrappedProgramComputedProtocolWindowInputs data program window)
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    (coverage : ProgramHashCallerCoverage data windows) :
    Realizes (FullStep program data.program) data.machine initial cells := by
  have protocol := wrapped_program_computed_protocol_inputs (by decide) (by decide) accepted inputs
  have memory := computed_protocol_memory_inputs (by decide) (by decide) accepted protocol
  have bounds := (ordered_hash_window_bounds ordered).1
  have cuts : ∀ window ∈ windows, window.lower % 4 = 0 ∧ window.upper % 4 = 0 ∧ 2 ≤ window.lower := by
    intro window member
    have bound := bounds window member
    have floor := hash_control_preparation_after_initial (scopes window member).preparation
    exact ⟨bound.2.2.1, bound.2.2.2, by omega⟩
  have localScopes : ∀ window ∈ windows, ComputedProtocolWindowInputs data program window := by
    intro window member
    exact wrapped_program_computed_protocol_window_inputs (by decide) (by decide) inputs.setup accepted
      inputs.publicProgram inputs.ordinaryProgram inputs.registry (scopes window member)
      (cuts window member).1 (cuts window member).2.1
  have covered := program_hash_worker_coverage (by decide) (by decide) inputs.setup accepted inputs.publicProgram
    inputs.ordinaryProgram inputs.registry cuts coverage
  have effects := mixed_memory_effects accepted memory
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  exact full_execution_at accepted memory profile.code effects.requests pc ledger permutation order history
    (fun _ member ordinary => ordinary_cycle_at accepted memory profile effects permutation order history member ordinary)
    (fun _ member => full_caller_cycle_at accepted memory profile.code commands localScopes
      (fun window included => ⟨(cuts window included).1, (cuts window included).2.1⟩)
      (fun worker included family live => (covered worker included family).mpr live)
      effects permutation order history member) terminal

end Airbender.UnifiedReduced.Caller.Proofs
