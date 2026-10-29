import Airbender.Review.Compiler.MachineTargets
import Airbender.Proofs.GKRProtocol.UnifiedProgramRows
import Airbender.Proofs.Initialization.Boundary

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384

/-- The public text decoder uses the combined unified stream registry. -/
theorem unified_decoder_fields (instruction : SailRV32.instruction) :
    NativeDecoder.UnifiedProgramRows.decoderFields instruction =
      UnifiedReduced.Caller.Stream.decoderFields instruction := by
  cases instruction <;>
    simp [NativeDecoder.UnifiedProgramRows.decoderFields,
      UnifiedReduced.Caller.Stream.decoderFields,
      UnifiedReduced.Caller.Stream.externalDecoderFields]
  case CSRReg args =>
    rcases args with ⟨csr, rs1, rd, operation⟩
    cases rs1 with
    | Regidx first =>
      cases rd with
      | Regidx destination =>
        cases operation <;> try rfl
        change BitVec 5 at first destination
        by_cases selected : csr = 0x7C0#12
        all_goals by_cases firstZero : first = 0#5
        all_goals by_cases destinationZero : destination = 0#5
        all_goals simp_all [UnifiedReduced.Modular.decoderFields,
          UnifiedReduced.Mixed.decoderFields, UnifiedReduced.decoderFields,
          Trace.decoderFields, JumpBranchSlt.decoderFields, ShiftBinop.decoderFields,
          UnifiedReduced.customDecoderFields, UnifiedReduced.Modular.mopDecoderFields,
          NonDeterminism.decoderFields, UnifiedReduced.arithmeticFields,
          DecoderData.mapFamily]

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The target's native initialization boundary supplies its boot inputs.
Public text supplies the program image. The RAM permutation stays separate. -/
theorem unified_initialization_inputs [Fact babyBearModulus.Prime]
    {initial : State} {text : List (BitVec 32)}
    {trace : UnifiedTrace babyBearModulus}
    (geometry : Initialization.Geometry Initialization.unified.layout)
    (windows : Initialization.Windows Initialization.unified.layout)
    {E : Type} [CommRing E] (embed : F →+* E)
    (additive : E) (weights : Fin 6 → E)
    (boundary : InitializationWitness E)
    (terminalRegisters : List (MemoryToken babyBearModulus))
    {capacity : Nat} {mask : NativeDecoder.ProgramRows.Mask}
    {columns : List (List F)}
    (profile : PublicProfile initial (Initialization.cells geometry windows))
    (programSetup : UnifiedProgramSetup initial text capacity mask columns)
    (physicalImage : ∃ image : List (MemoryToken babyBearModulus),
      initialImage initial (Initialization.cells geometry windows) = some image)
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0))
    (romSetup : trace.rom = UnifiedReduced.Setup.table initial)
    (initializationBoundary : InitializationBoundary Initialization.unified
      (Initialization.parametersFor embed additive weights windows)
      boundary terminalRegisters trace) :
    UnifiedReduced.BootInputsWith UnifiedReduced.Caller.Stream.decoderFields
      trace initial (Initialization.cells geometry windows)
      (NativeDecoder.UnifiedProgramRows.ordinaryProgramOf initial text) := by
  have seed : trace.initialMemory =
      ROMView.nativeBootImage (Initialization.cells geometry windows) :=
    initializationBoundary.1.trans (Initialization.Proofs.computed_seed trace
      Initialization.unified.layout geometry windows embed additive weights
      boundary.raw terminalRegisters)
  have image := NativeDecoder.UnifiedProgramRows.Proofs.ordinary_program_image
    initial text programSetup.image programSetup.size
  have decoder : NativeDecoder.UnifiedProgramRows.decoderFields =
      UnifiedReduced.Caller.Stream.decoderFields := funext unified_decoder_fields
  rw [decoder] at image
  exact {
    distinct := ExternalBoundary.Initialization.Proofs.cells_distinct
      (windows.selection geometry)
    aligned := ExternalBoundary.Initialization.Proofs.aligned
      (windows.selection geometry)
    profile := profile.bootProfile
    image := physicalImage
    seed := seed
    initialPC := initialBoundary
    programImage := ⟨_, image⟩
    setup := romSetup }

end Airbender.Compiler.MachineTargets.Proofs
