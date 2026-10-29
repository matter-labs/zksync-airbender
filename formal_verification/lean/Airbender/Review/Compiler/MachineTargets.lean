import Airbender.Review.Compiler.PublicProgramSetup
import Airbender.Review.Compiler.ROMDomain
import Airbender.Review.Trace.FullUnsigned
import Airbender.Review.Trace.Modular.ReducedUse
import Airbender.Review.Trace.UnifiedReduced.StreamCalls
import Airbender.Review.Trace.Workers.Keccak.SplitRequests
import Airbender.Review.Helpers.Delegation.MixedMemory
import Airbender.Review.Helpers.UnifiedReduced.MixedMemory
import Airbender.Review.Circuits.Initialization.Artifact
import Airbender.Review.Circuits.Initialization.Boundary

namespace Airbender.Compiler.MachineTargets
open Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
-- Proposition binders retain premise names for review and obligation tracking.
set_option linter.unusedVariables false
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
variable [Fact babyBearModulus.Prime]

abbrev F := ZMod babyBearModulus

/-- Raw native initialization columns and GKR wires. The public windows and
linearization challenges are quantified separately by each target. -/
structure InitializationWitness (E : Type) where
  raw : Initialization.Raw babyBearModulus
  wires : Initialization.Wires E

/-- Bind the execution boundary to the actual imported initialization circuit.
The logical RAM permutation below remains separate from GKR product equality. -/
def InitializationBoundary {Kind E : Type} [CircuitLayout Kind] [CommRing E]
    (artifact : Initialization.Artifact)
    (parameters : Initialization.Parameters babyBearModulus E)
    (witness : InitializationWitness E)
    (terminalRegisters : List (MemoryToken babyBearModulus))
    (trace : Data babyBearModulus Kind) : Prop :=
  trace.initialMemory = ROMView.nativeBootImage ExternalBoundary.Initialization.registers ++
      Initialization.ramTokens artifact.layout parameters witness.raw .initial ∧
    trace.terminalMemory = terminalRegisters ++
      Initialization.ramTokens artifact.layout parameters witness.raw .terminal

/-- Public Sail configuration and starting profile shared by all machines.
No row operands, worker controls, expected outputs or witness history occur. -/
structure PublicProfile (initial : State) (cells : List Cell) : Prop where
  bootProfile : InitialProfile initial cells
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address
  landingPadDisabled : ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0

def pooledCalls (trace : PooledTrace babyBearModulus) :=
  (trace.rows.filter fun row => row.family == .addSub &&
    decide (Delegation.Requests.Selected row.assignment)).map fun row =>
      Delegation.Requests.caller row.assignment

def pooledSteps (trace : PooledTrace babyBearModulus) :=
  trace.rows.flatMap fun row => (Delegation.Caller.machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

def unifiedCalls (trace : UnifiedTrace babyBearModulus) :=
  (trace.rows.filter fun row => decide
    (UnifiedReduced.Caller.Selected row.assignment)).map fun row =>
      UnifiedReduced.Caller.request row.assignment

def unifiedSteps (trace : UnifiedTrace babyBearModulus) :=
  trace.rows.flatMap fun row => (UnifiedReduced.Caller.machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

/-- Exact native CPU/worker equations and the three permitted logical argument
boundaries. Decoder matching is supplied against public text-derived columns
in the targets; no per-row decoded instruction is assumed here. -/
structure UnrolledAcceptance (trace : PooledTrace babyBearModulus)
    (workers : Delegation.MemoryData babyBearModulus)
    (extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus))
    (extraRequests : List (Delegation.Requests.Request babyBearModulus)) : Prop where
  cpuEquations : ∀ row ∈ trace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints trace.rom)
  cpuActive : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1
  workerEquations : ∀ row ∈ workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints workers.setup)
  workerActive : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1
  states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start)
  requests : Delegation.Requests.Matching (pooledCalls trace)
    (workers.rows.map Delegation.Requests.fulfillment ++ extraRequests)
  ram : (trace.initialMemory ++
      (pooledSteps trace ++ workers.steps ++ extraSteps).map Prod.snd).Perm
    (trace.terminalMemory ++
      (pooledSteps trace ++ workers.steps ++ extraSteps).map Prod.fst)

structure UnifiedAcceptance (trace : UnifiedTrace babyBearModulus)
    (workers : Delegation.MemoryData babyBearModulus) : Prop where
  cpuEquations : ∀ row ∈ trace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints trace.rom)
  cpuActive : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1
  workerEquations : ∀ row ∈ workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints workers.setup)
  workerActive : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1
  states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start)
  requests : Delegation.Requests.Matching (unifiedCalls trace)
    (workers.rows.map Delegation.Requests.fulfillment)
  ram : (trace.initialMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
    (trace.terminalMemory ++ (unifiedSteps trace ++ workers.steps).map Prod.fst)

/-- Exact public provenance of a fixed native setup table, including physical
padding. The source is the retained complete JSON, not a semantic table recipe.
This public premise is an importer/setup obligation, not witness soundness. -/
def FixedSetup (source : String) (table : Table F (fields width)) : Prop :=
  ∃ artifact : Airbender.Setup.Artifact,
    Airbender.Setup.parse source = .ok artifact ∧ artifact.columns.size = width ∧
    ∀ row : Vector F width, table.toRaw.Soundness #[] row ↔
      ∃ index : Fin artifact.trace_len, ∀ column : Fin width,
        row[column] = (Airbender.Setup.signedValue
          ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)

def reducedCallerFields (instruction : SailRV32.instruction) :
    Option (DecoderData Delegation.Family) := do
  let data ← Delegation.Caller.decoderFields instruction
  if data.family = .blakeRound then some data else none

def reducedProgram (initial : State) (text : List (BitVec 32))
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle) :
    AddSub.Modular.External.Caller.ReducedUse.Program where
  ordinary := NativeDecoder.ProgramRows.programOf .reduced initial text
  callers := FullUnsigned.entriesWith reducedCallerFields text
  bundles := bundles

def unifiedProgram (initial : State) (text : List (BitVec 32))
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle) :
    UnifiedReduced.Caller.DelegationUse.Program where
  ordinary := NativeDecoder.UnifiedProgramRows.ordinaryProgramOf initial text
  callers := FullUnsigned.entriesWith Delegation.Caller.decoderFields text
  bundles := bundles

/-- Full unsigned production target. Split Keccak is included in the machine
relation and native worker pool. Only special5 is publicly excluded. The named
premises expose fixed setup, native circuits, public program binding, exact
lookup/request/RAM matching and standalone initialization separately. -/
def UnrolledFullUnsigned : Prop :=
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
    ∀ (publicProfile : PublicProfile initial cells)
      (programSetup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
      (decoderLookup : UnrolledDecoderExactLookup trace masks columns)
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
      (nativeAcceptance : UnrolledAcceptance trace workers splitWorkers.steps
        (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
      (initializationGates : Initialization.Accepted Initialization.standalone
        parameters boundary.raw boundary.wires)
      (initializationBoundary : InitializationBoundary Initialization.standalone
        parameters boundary terminalRegisters trace)
      (streamPorts : NonDeterminism.Pooled.StreamPorts trace stream),
    FullUnsigned.Realizes stream program trace initial cells (ROMView.token initial)

/-- Reduced unrolled production target: four CPU families, external input,
modular operations and the extended-round worker share one initialized history. -/
def UnrolledReduced : Prop :=
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
    ∀ (publicProfile : PublicProfile initial cells)
      (programSetup : UnrolledProgramSetup .reduced initial text capacity masks columns)
      (decoderLookup : UnrolledDecoderExactLookup trace masks columns)
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
      (nativeAcceptance : UnrolledAcceptance trace workers [] [])
      (initializationGates : Initialization.Accepted Initialization.standalone
        parameters boundary.raw boundary.wires)
      (initializationBoundary : InitializationBoundary Initialization.standalone
        parameters boundary terminalRegisters trace)
      (streamPorts : NonDeterminism.Pooled.StreamPorts trace stream),
    AddSub.Modular.External.Caller.ReducedRealizes stream program.ordinary program.callers
      trace initial cells (ROMView.token initial)

/-- Unified production target: one native CPU circuit combines ordinary,
TRIADD/XORROT, modular, external-input and complete delegation semantics. Its
inline initialization circuit supplies the same shared RAM boundary. -/
def Unified : Prop :=
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
    ∀ (publicProfile : PublicProfile initial cells)
      (programSetup : UnifiedProgramSetup initial text capacity mask columns)
      (decoderLookup : UnifiedDecoderExactLookup trace mask columns)
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
      (nativeAcceptance : UnifiedAcceptance trace workers)
      (initializationGates : Initialization.Accepted Initialization.unified
        parameters boundary.raw boundary.wires)
      (initializationBoundary : InitializationBoundary Initialization.unified
        parameters boundary terminalRegisters trace)
      (streamPorts : UnifiedReduced.Caller.Stream.StreamPorts trace stream),
    UnifiedReduced.Caller.Stream.Realizes stream program.ordinary program.callers
      trace initial cells (ROMView.token initial)

end Airbender.Compiler.MachineTargets
