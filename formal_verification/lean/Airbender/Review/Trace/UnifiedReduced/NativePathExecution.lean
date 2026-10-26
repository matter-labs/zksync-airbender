import Airbender.Proofs.UnifiedReduced.NativePathExecution

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- Conditional whole execution along the actual branch/jump/repeated-PC path.
`HashCommands` explicitly restricts native controller reads and separates G
block bases; their enforcement by the restored circuits is not proved here. Public
program bytes, initialized memory, configuration/retirement and the separate
bigint command contract remain explicit. No occurrence plan or desired result
is supplied. Complete algorithm grouping requires its separate span profile. -/
theorem native_path_execution_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputs data program initial ca oa cells)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (hashes : HashCommands data) :
    Realizes (FullStep program data.program) data.machine initial cells :=
  Proofs.native_path_execution accepted inputs profile pc commands hashes

end Airbender.UnifiedReduced.Caller
