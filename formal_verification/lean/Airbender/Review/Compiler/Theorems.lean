import Airbender.Proofs.GKRProtocol.NativeMachineAcceptance
import Airbender.Proofs.FullUnsigned.Target
import Airbender.Proofs.Reduced.MachineTarget
import Airbender.Proofs.UnifiedReduced.MachineTarget

namespace Airbender.Compiler.MachineTargets
open Trace Reference.RiscV.Sail Reference.Sail NativeProgramSetup
set_option warningAsError true
set_option Elab.async false
-- Keep premise names in the quantified review statements.
set_option linter.unusedVariables false
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Cached native certificates supply CPU acceptance and exact decoder lookup.
The remaining public setup, matching and initialization premises stay explicit. -/
theorem unrolled_full_from_native :
  ∀ [Fact babyBearModulus.Prime], ∀ (initial : State) (text : List (BitVec 32))
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle)
    (splitBundles : List Keccak.Split.Bundle)
    (trace : PooledTrace babyBearModulus)
    (workers : Delegation.MemoryData babyBearModulus)
    (splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus)
    (terminalRegisters : List (MemoryToken babyBearModulus))
    (geometry : Initialization.Geometry Initialization.standalone.layout)
    (windows : Initialization.Windows Initialization.standalone.layout)
    (E : Type) [CommRing E] (embed : F →+* E)
    (additive : E) (weights : Fin 6 → E) (boundary : InitializationWitness E)
    (capacity : Nat) (masks : PooledFamily → NativeDecoder.ProgramRows.Mask)
    (columns : PooledFamily → List (List F)) (stream : List (BitVec 32)),
    let cells := Initialization.cells geometry windows
    let parameters := Initialization.parametersFor embed additive weights windows
    let program := FullUnsigned.Program.ofText initial text bundles splitBundles
    ∀ (certificates : List (PooledExecution.ProgramLogicalRowCertificate
        (unrolledProgramLookupRows initial columns)))
      (nativeArguments : UnrolledNativeArguments initial columns certificates trace workers splitWorkers.steps
        (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
      (publicProfile : PublicProfile initial cells)
      (programSetup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
      (noSpecial5 : FullUnsigned.NoSpecial5Call initial text)
      (validUse : FullUnsigned.ValidDelegationUse program initial)
      (loads : NoDiscardedLoads program.ordinary)
      (initialBoundary : trace.initial = PCState.boundary 0 (4, 0))
      (stateClosure : VerifierBoundary.BootClosure trace.initial
        (trace.rows.map Row.start) (trace.rows.map Row.finish))
      (romDomain : ROMNative.WordFullPublic.CoversROM cells)
      (wordSetup : ∃ image, initialImage initial cells = some image ∧
        trace.rom.wordMemory = ROM.table cells image)
      (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
      (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
      (workerFamilies : ∀ row ∈ workers.rows, FullUnsigned.standardCall row.family)
      (splitColumnParitySetup : FixedSetup
        (include_str "../../../artifacts/setup/keccak-column-parity.json") splitWorkers.setup.columnParity)
      (splitThetaRhoSetup : FixedSetup
        (include_str "../../../artifacts/setup/keccak-theta-rho.json") splitWorkers.setup.thetaRho)
      (splitChi5Setup : FixedSetup
        (include_str "../../../artifacts/setup/keccak-chi5.json") splitWorkers.setup.chi5)
      (splitEquations : Keccak.Split.Native.EquationsHold
        splitWorkers.cached splitWorkers.setup splitWorkers.rows)
      (splitActive : ∀ row ∈ splitWorkers.rows,
        row.assignment (row.columns splitWorkers.cached).execute = 1)
      (initializationGates : Initialization.Accepted Initialization.standalone
        parameters boundary.raw boundary.wires)
      (initializationBoundary : InitializationBoundary Initialization.standalone
        parameters boundary terminalRegisters trace)
      (streamPorts : NonDeterminism.Pooled.StreamPorts trace stream),
    FullUnsigned.Realizes stream program trace initial cells (ROMView.token initial) := by
  intro prime initial text bundles splitBundles trace workers splitWorkers terminalRegisters geometry windows E ring embed additive weights boundary capacity masks columns stream
  dsimp only
  intro certificates nativeArguments publicProfile programSetup noSpecial5 validUse loads initialBoundary stateClosure romDomain wordSetup subwordSetup workerSetup workerFamilies splitColumnParitySetup splitThetaRhoSetup splitChi5Setup splitEquations splitActive initializationGates initializationBoundary streamPorts
  obtain ⟨nativeAcceptance, decoderLookup⟩ :=
    unrolled_acceptance_from_native programSetup nativeArguments romDomain wordSetup subwordSetup initialBoundary
  exact Proofs.unrolled_full_soundness initial text bundles splitBundles trace workers splitWorkers terminalRegisters geometry windows E embed additive weights boundary capacity masks columns stream
    publicProfile programSetup decoderLookup noSpecial5 validUse loads initialBoundary stateClosure romDomain wordSetup subwordSetup workerSetup workerFamilies splitColumnParitySetup splitThetaRhoSetup splitChi5Setup splitEquations splitActive nativeAcceptance initializationGates initializationBoundary streamPorts

/-- Cached native certificates supply CPU acceptance and exact decoder lookup.
The remaining public setup, matching and initialization premises stay explicit. -/
theorem unrolled_reduced_from_native :
  ∀ [Fact babyBearModulus.Prime], ∀ (initial : State) (text : List (BitVec 32))
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle)
    (trace : PooledTrace babyBearModulus)
    (workers : Delegation.MemoryData babyBearModulus)
    (terminalRegisters : List (MemoryToken babyBearModulus))
    (geometry : Initialization.Geometry Initialization.standalone.layout)
    (windows : Initialization.Windows Initialization.standalone.layout)
    (E : Type) [CommRing E] (embed : F →+* E)
    (additive : E) (weights : Fin 6 → E) (boundary : InitializationWitness E)
    (capacity : Nat) (masks : PooledFamily → NativeDecoder.ProgramRows.Mask)
    (columns : PooledFamily → List (List F)) (stream : List (BitVec 32)),
    let cells := Initialization.cells geometry windows
    let parameters := Initialization.parametersFor embed additive weights windows
    let program := reducedProgram initial text bundles
    ∀ (certificates : List (PooledExecution.ProgramLogicalRowCertificate
        (unrolledProgramLookupRows initial columns)))
      (nativeArguments : UnrolledNativeArguments initial columns certificates trace workers [] [])
      (publicProfile : PublicProfile initial cells)
      (programSetup : UnrolledProgramSetup .reduced initial text capacity masks columns)
      (validUse : AddSub.Modular.External.Caller.ReducedUse.ValidDelegationUse program initial)
      (loads : NoDiscardedLoads program.ordinary)
      (initialBoundary : trace.initial = PCState.boundary 0 (4, 0))
      (stateClosure : VerifierBoundary.BootClosure trace.initial
        (trace.rows.map Row.start) (trace.rows.map Row.finish))
      (romDomain : ROMNative.WordFullPublic.CoversROM cells)
      (wordSetup : ∃ image, initialImage initial cells = some image ∧
        trace.rom.wordMemory = ROM.table cells image)
      (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
      (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
      (cpuFamilies : ∀ row ∈ trace.rows,
        AddSub.Modular.External.Caller.reducedFamily row.family = true)
      (workerFamilies : ∀ row ∈ workers.rows, row.family = .blakeRound)
      (initializationGates : Initialization.Accepted Initialization.standalone
        parameters boundary.raw boundary.wires)
      (initializationBoundary : InitializationBoundary Initialization.standalone
        parameters boundary terminalRegisters trace)
      (streamPorts : NonDeterminism.Pooled.StreamPorts trace stream),
    AddSub.Modular.External.Caller.ReducedRealizes stream program.ordinary program.callers
      trace initial cells (ROMView.token initial) := by
  intro prime initial text bundles trace workers terminalRegisters geometry windows E ring embed additive weights boundary capacity masks columns stream
  dsimp only
  intro certificates nativeArguments publicProfile programSetup validUse loads initialBoundary stateClosure romDomain wordSetup subwordSetup workerSetup cpuFamilies workerFamilies initializationGates initializationBoundary streamPorts
  obtain ⟨nativeAcceptance, decoderLookup⟩ :=
    unrolled_acceptance_from_native programSetup nativeArguments romDomain wordSetup subwordSetup initialBoundary
  exact Proofs.unrolled_reduced_soundness initial text bundles trace workers terminalRegisters geometry windows E embed additive weights boundary capacity masks columns stream
    publicProfile programSetup decoderLookup validUse loads initialBoundary stateClosure romDomain wordSetup subwordSetup workerSetup cpuFamilies workerFamilies nativeAcceptance initializationGates initializationBoundary streamPorts

/-- Cached native certificates supply CPU acceptance and exact decoder lookup.
The remaining public setup, matching and initialization premises stay explicit. -/
theorem unified_from_native :
  ∀ [Fact babyBearModulus.Prime], ∀ (initial : State) (text : List (BitVec 32))
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle)
    (trace : UnifiedTrace babyBearModulus)
    (workers : Delegation.MemoryData babyBearModulus)
    (terminalRegisters : List (MemoryToken babyBearModulus))
    (geometry : Initialization.Geometry Initialization.unified.layout)
    (windows : Initialization.Windows Initialization.unified.layout)
    (E : Type) [CommRing E] (embed : F →+* E)
    (additive : E) (weights : Fin 6 → E) (boundary : InitializationWitness E)
    (capacity : Nat) (mask : NativeDecoder.ProgramRows.Mask)
    (columns : List (List F)) (stream : List (BitVec 32)),
    let cells := Initialization.cells geometry windows
    let parameters := Initialization.parametersFor embed additive weights windows
    let program := unifiedProgram initial text bundles
    ∀ (certificates : List (UnifiedExecution.ProgramLogicalRowCertificate
        (unifiedLookupRows initial columns)))
      (nativeArguments : UnifiedNativeArguments initial columns certificates trace workers)
      (publicProfile : PublicProfile initial cells)
      (programSetup : UnifiedProgramSetup initial text capacity mask columns)
      (noSpecial5 : NativeDecoder.ProgramRows.NoSpecial5Call
        (NativeDecoder.UnifiedProgramRows.callerProgramOf initial text))
      (validUse : UnifiedReduced.Caller.Stream.ValidDelegationUse program initial)
      (loads : ∀ entry ∈ program.ordinary, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
        entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4))
      (initialBoundary : trace.initial = PCState.boundary 0 (4, 0))
      (physicalImage : ∃ image : List (MemoryToken babyBearModulus),
        initialImage initial cells = some image)
      (romSetup : trace.rom = UnifiedReduced.Setup.table initial)
      (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
      (initializationGates : Initialization.Accepted Initialization.unified
        parameters boundary.raw boundary.wires)
      (initializationBoundary : InitializationBoundary Initialization.unified
        parameters boundary terminalRegisters trace)
      (streamPorts : UnifiedReduced.Caller.Stream.StreamPorts trace stream),
    UnifiedReduced.Caller.Stream.Realizes stream program.ordinary program.callers
      trace initial cells (ROMView.token initial) := by
  intro prime initial text bundles trace workers terminalRegisters geometry windows E ring embed additive weights boundary capacity mask columns stream
  dsimp only
  intro certificates nativeArguments publicProfile programSetup noSpecial5 validUse loads initialBoundary physicalImage romSetup workerSetup initializationGates initializationBoundary streamPorts
  obtain ⟨nativeAcceptance, decoderLookup⟩ :=
    unified_acceptance_from_native programSetup nativeArguments romSetup initialBoundary
  exact Proofs.unified_soundness initial text bundles trace workers terminalRegisters geometry windows E embed additive weights boundary capacity mask columns stream
    publicProfile programSetup decoderLookup noSpecial5 validUse loads initialBoundary physicalImage romSetup workerSetup nativeAcceptance initializationGates initializationBoundary streamPorts

end Airbender.Compiler.MachineTargets
