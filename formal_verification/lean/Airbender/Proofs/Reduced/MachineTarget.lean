import Airbender.Proofs.Reduced.PublicAcceptance

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The public reduced target follows from exact native acceptance, public
lookup, reachable supported use and standalone initialization. -/
theorem unrolled_reduced_soundness : UnrolledReduced := by
  intro prime initial text bundles trace workers terminalRegisters geometry windows
    E ring embed additive weights boundary capacity masks columns stream
  dsimp only
  intro publicProfile programSetup decoderLookup validUse loads initialBoundary stateClosure
    _romDomain wordSetup subwordSetup workerSetup cpuFamilies workerFamilies nativeAcceptance
    _initializationGates initializationBoundary streamPorts
  let data : Delegation.Caller.RequestTrace babyBearModulus :=
    ⟨trace, workers, (reducedProgram initial text bundles).callers⟩
  have initialBound : trace.initial.word.lo < limbBase := by
    rw [initialBoundary]
    change (0 : Nat) < 65536
    omega
  have accepted := reduced_native_acceptance bundles programSetup decoderLookup nativeAcceptance cpuFamilies initialBound
  have boot := reduced_initialization_inputs geometry windows embed additive weights boundary
    terminalRegisters publicProfile programSetup loads initialBoundary wordSetup subwordSetup stateClosure initializationBoundary
  have code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0 :=
    text_caller_code reducedCallerFields text programSetup.size
  exact AddSub.Modular.External.Caller.Proofs.supported_native_path_execution
    (data := data) accepted boot
    ⟨_, reduced_caller_image programSetup.image programSetup.size⟩
    workerSetup code cpuFamilies workerFamilies rfl validUse stream streamPorts

end Airbender.Compiler.MachineTargets.Proofs
