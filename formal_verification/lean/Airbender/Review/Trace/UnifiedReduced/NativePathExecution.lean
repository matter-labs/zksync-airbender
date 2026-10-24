import Airbender.Proofs.UnifiedReduced.NativePathExecution

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- Native successful-call enforcement yields one whole execution along the
actual branch/jump/repeated-PC path. Public program bytes, initialized memory,
configuration/retirement and the separate bigint command contract remain
explicit. No occurrence schedule, prepared controller value, G pointer
separation, or round mask is a caller premise. Complete algorithm grouping
remains a separate protocol-span property. -/
theorem native_path_execution_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputs data program initial ca oa cells)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) :
    Realizes (FullStep program data.program) data.machine initial cells :=
  Proofs.native_path_execution accepted inputs profile pc commands

end Airbender.UnifiedReduced.Caller
