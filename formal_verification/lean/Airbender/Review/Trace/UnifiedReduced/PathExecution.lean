import Airbender.Proofs.UnifiedReduced.PathExecution

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- A per-trace occurrence schedule and native participation yield whole mixed
    execution along actual PCs, including branch/jump/repeated-PC loops. Every
    caller uses its complete independent family reference; ordinary register,
    link and RAM effects remain in the same execution. The final PC and every
    tracked terminal cell agree with the native boundaries. Existing code,
    memory/configuration, successful-retirement and bigint F02 profiles remain
    explicit. Complete protocol-span algorithms use the separate span layer. -/
theorem path_execution_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data initial ca oa cells program plans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) :
    Realizes (FullStep program data.program) data.machine initial cells :=
  Proofs.path_execution accepted inputs profile pc commands

end Airbender.UnifiedReduced.Caller
