import Airbender.Proofs.UnifiedReduced.StreamPublicAcceptance

namespace Airbender.Compiler.MachineTargets.Proofs
open Arithmetic Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The public Unified target follows from its exact native acceptance,
lookup, supported-use and initialization premises. -/
theorem unified_soundness : Unified := by
  intro prime initial text bundles trace workers terminalRegisters geometry windows
    E ring embed additive weights boundary capacity mask columns stream
  dsimp only
  intro publicProfile programSetup decoderLookup noSpecial5 validUse loads
    initialBoundary physicalImage romSetup workerSetup nativeAcceptance
    initializationGates initializationBoundary streamPorts
  let data : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
    ⟨trace, workers, (unifiedProgram initial text bundles).callers⟩
  have initialBound : trace.initial.word.lo < limbBase := by
    rw [initialBoundary]
    change (0 : Nat) < 65536
    omega
  have accepted := unified_native_acceptance bundles programSetup decoderLookup nativeAcceptance initialBound
  have boot := unified_initialization_inputs geometry windows embed additive weights boundary
    terminalRegisters publicProfile programSetup physicalImage initialBoundary romSetup initializationBoundary
  have profile := unified_rom_profile (data := data) geometry windows publicProfile programSetup.size rfl loads
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) initial =
      .ok trace.initial.word.toBitVec initial := by
    rw [initialBoundary]
    exact publicProfile.bootProfile.pc
  exact UnifiedReduced.Caller.Stream.Proofs.supported_native_path_execution
    (data := data) accepted boot
    ⟨_, unified_caller_image initial text programSetup.image programSetup.size⟩
    workerSetup profile pc rfl validUse stream streamPorts

end Airbender.Compiler.MachineTargets.Proofs
