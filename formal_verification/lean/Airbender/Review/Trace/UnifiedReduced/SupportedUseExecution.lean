import Airbender.Proofs.UnifiedReduced.SupportedUseExecution

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- Whole native-path execution for programs satisfying the public supported-use
contract. Bigint commands and hash controller/base restrictions are derived by
induction over exact native prefixes. Public initialization, the ordinary memory
profile, decoder/setup bindings and exact logical matching remain explicit.
The covered wrappers are bigint, G and extended round; split Keccak is deferred
(F12). No production circuit is changed to obtain this result. -/
theorem supported_path_execution_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : DelegationUse.Program}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program.ordinary)
    (inputs : NativeMemoryInputs data program.ordinary initial ca oa cells)
    (profile : RetirementProfile data program.ordinary initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (registry : data.program = program.callers) (valid : ValidDelegationUse program initial) :
    Realizes (FullStep program.ordinary program.callers) data.machine initial cells :=
  Proofs.supported_path_execution accepted inputs profile pc registry valid

end Airbender.UnifiedReduced.Caller
