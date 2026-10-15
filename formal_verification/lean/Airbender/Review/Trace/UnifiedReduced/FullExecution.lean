import Airbender.Proofs.UnifiedReduced.FullExecution

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- Whole mixed execution from the actual public initial state to the native
    terminal PC/cells. Ordinary clauses retain their original Sail semantics;
    every issued custom CSR executes the complete independent family reference
    and retires its PC in this same chain. Existing preparation/coverage derives
    hash ABI and round masks; initialized matching derives actual reads and writes.

    F02's temporary bigint command binding and F03's occurrence ledger remain
    explicit. The existing tracked-RAM/code/configuration and public protocol
    profiles remain in scope; their enforcement findings are not circuit fixes. -/
theorem full_execution_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
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
    Realizes (FullStep program data.program) data.machine initial cells :=
  Proofs.full_execution accepted inputs profile pc commands ledger scopes ordered coverage

end Airbender.UnifiedReduced.Caller
