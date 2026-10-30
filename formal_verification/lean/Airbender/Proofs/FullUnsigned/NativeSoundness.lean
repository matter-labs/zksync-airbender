import Airbender.Proofs.FullUnsigned.SupportedInduction

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Full native execution follows from public supported use and the canonical
setup interpretation. No private worker input or execution result is a premise. -/
theorem unrolled_full_supported_execution [Fact babyBearModulus.Prime]
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle) (splitBundles : List Keccak.Split.Bundle)
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus} {cells : List Cell}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (boot : PooledBootInputs trace initial cells
      (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text) AddSub.Modular.External.decoderFields)
    (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (workerFamilies : ∀ worker ∈ workers.rows, FullUnsigned.standardCall worker.family)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (control : Keccak.Split.Native.ControlSetupFacts splitWorkers.setup)
    (fixedEquations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached Keccak.Split.Native.Proofs.fixedSetup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (valid : FullUnsigned.ValidDelegationUse (FullUnsigned.Program.ofText initial text bundles splitBundles) initial)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    FullUnsigned.Realizes stream (FullUnsigned.Program.ofText initial text bundles splitBundles)
      trace initial cells (ROMView.token initial) := by
  obtain ⟨standard, split⟩ := unrolled_full_supported_native_inputs bundles splitBundles setup lookup accepted excluded boot
    workerSetup workerFamilies equations control fixedEquations active valid stream ports
  exact (unrolled_full_boot_execution_of_native_inputs bundles splitBundles setup lookup accepted excluded boot
    workerSetup workerFamilies equations control fixedEquations active standard split stream ports).1

/-- The original full target has one remaining importer obligation: parsed
fixed sources must imply the canonical setup interpretation. The public target,
its initialization boundary and exact native matching premises stay unchanged. -/
theorem unrolled_full_soundness_of_setup_interpretation
    (interpretation : ∀ [Fact babyBearModulus.Prime], ∀ data : Keccak.Split.Native.MemoryData babyBearModulus,
      FixedSetup (include_str "../../../artifacts/setup/keccak-column-parity.json") data.setup.columnParity →
      FixedSetup (include_str "../../../artifacts/setup/keccak-theta-rho.json") data.setup.thetaRho →
      FixedSetup (include_str "../../../artifacts/setup/keccak-chi5.json") data.setup.chi5 →
      Keccak.Split.Native.EquationsHold data.cached data.setup data.rows →
      Keccak.Split.Native.ControlSetupFacts data.setup ∧
        Keccak.Split.Native.EquationsHold data.cached Keccak.Split.Native.Proofs.fixedSetup data.rows) :
    UnrolledFullUnsigned := by
  intro prime initial text bundles splitBundles trace workers splitWorkers terminalRegisters geometry windows
    E ring embed additive weights boundary capacity masks columns stream
  dsimp only
  intro publicProfile programSetup decoderLookup noSpecial5 validUse loads initialBoundary stateClosure
    _romDomain wordSetup subwordSetup workerSetup workerFamilies splitColumnParitySetup splitThetaRhoSetup
    splitChi5Setup splitEquations splitActive nativeAcceptance _initializationGates initializationBoundary streamPorts
  obtain ⟨control, fixedEquations⟩ := interpretation splitWorkers splitColumnParitySetup splitThetaRhoSetup
    splitChi5Setup splitEquations
  have boot := unrolled_full_initialization_inputs geometry windows embed additive weights boundary terminalRegisters
    publicProfile programSetup loads initialBoundary wordSetup subwordSetup stateClosure initializationBoundary
  exact unrolled_full_supported_execution bundles splitBundles programSetup decoderLookup nativeAcceptance noSpecial5 boot
    workerSetup workerFamilies splitEquations control fixedEquations splitActive validUse stream streamPorts

end Airbender.Compiler.MachineTargets.Proofs
