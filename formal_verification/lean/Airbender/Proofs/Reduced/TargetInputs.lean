import Airbender.Proofs.UnifiedReduced.StreamPublicCallers
import Airbender.Proofs.Initialization.PooledInputs
import Airbender.Proofs.Trace.ReducedPublicProgram

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

/-- The public reduced text uses the stream-aware four-family program image. -/
theorem reduced_ordinary_image {initial : State} {text : List (BitVec 32)}
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    programImageRunWith AddSub.Modular.External.Caller.reducedDecoderFields initial
      ((NativeDecoder.ProgramRows.programOf .reduced initial text).map ProgramEntry.pc) =
        some (NativeDecoder.ProgramRows.programOf .reduced initial text) :=
  NativeDecoder.ProgramRows.Proofs.program_image .reduced initial text image size

/-- The reduced caller filter retains exactly the extended-round reference decoder. -/
theorem reduced_caller_metadata {instruction : SailRV32.instruction}
    {data : DecoderData Delegation.Family}
    (fields : reducedCallerFields instruction = some data) :
    Delegation.Caller.decoderFields instruction = some data ∧ data.family = .blakeRound := by
  unfold reducedCallerFields at fields
  cases native : Delegation.Caller.decoderFields instruction with
  | none => simp [native] at fields
  | some found =>
    simp only [native, bind, Option.bind] at fields
    split at fields
    next family => cases fields; exact ⟨rfl, family⟩
    next other => simp at fields

/-- The reduced caller registry retains its original public Sail sources. -/
theorem reduced_caller_image {initial : State} {text : List (BitVec 32)}
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    Delegation.Caller.programImage initial
      ((FullUnsigned.entriesWith reducedCallerFields text).map ProgramEntry.pc) =
        some (FullUnsigned.entriesWith reducedCallerFields text) := by
  apply Airbender.Compiler.PublicProgram.image_run
  intro entry member
  have source := text_caller_sources reducedCallerFields initial text image size entry member
  exact ⟨source.bytes, source.decoded, (reduced_caller_metadata source.fields).1⟩

/-- The target's native boundary supplies complete stream-aware reduced boot inputs. -/
theorem reduced_initialization_inputs
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [Fact babyBearModulus.Prime]
    {initial : State} {text : List (BitVec 32)}
    {bundles : List UnifiedReduced.Caller.DelegationUse.Bundle}
    {trace : PooledTrace babyBearModulus}
    (geometry : Initialization.Geometry Initialization.standalone.layout)
    (windows : Initialization.Windows Initialization.standalone.layout)
    {E : Type} [CommRing E] (embed : F →+* E)
    (additive : E) (weights : Fin 6 → E) (boundary : InitializationWitness E)
    (terminalRegisters : List (MemoryToken babyBearModulus))
    {capacity : Nat} {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List F)}
    (profile : PublicProfile initial (Initialization.cells geometry windows))
    (programSetup : UnrolledProgramSetup .reduced initial text capacity masks columns)
    (loads : NoDiscardedLoads (reducedProgram initial text bundles).ordinary)
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0))
    (wordSetup : ∃ image, initialImage initial (Initialization.cells geometry windows) = some image ∧
      trace.rom.wordMemory = ROM.table (Initialization.cells geometry windows) image)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (stateClosure : VerifierBoundary.BootClosure trace.initial
      (trace.rows.map Row.start) (trace.rows.map Row.finish))
    (initializationBoundary : InitializationBoundary Initialization.standalone
      (Initialization.parametersFor embed additive weights windows)
      boundary terminalRegisters trace) :
    PooledBootInputs trace initial (Initialization.cells geometry windows)
      (reducedProgram initial text bundles).ordinary
      AddSub.Modular.External.Caller.reducedDecoderFields := by
  have seed : trace.initialMemory = ROMView.nativeBootImage (Initialization.cells geometry windows) :=
    initializationBoundary.1.trans (Initialization.Proofs.computed_seed trace
      Initialization.standalone.layout geometry windows embed additive weights boundary.raw terminalRegisters)
  have entries : NativeDecoder.ProgramRows.programOf .reduced initial text =
      FullUnsigned.entriesWith NativeDecoder.ProgramRows.Config.reduced.fields text := rfl
  refine {
    registers := ExternalBoundary.Initialization.Proofs.all_registers (windows.selection geometry)
    ordinary := profile.ordinary
    configuration := profile.configuration
    landingPadDisabled := profile.landingPadDisabled
    code := ?_
    loads := loads
    distinct := ExternalBoundary.Initialization.Proofs.cells_distinct (windows.selection geometry)
    aligned := ExternalBoundary.Initialization.Proofs.aligned (windows.selection geometry)
    programImage := ⟨_, reduced_ordinary_image programSetup.image programSetup.size⟩
    profile := profile.bootProfile
    seed := seed
    initialBoundary := initialBoundary
    physicalImage := wordSetup
    subwordSetup := subwordSetup
    verifierBoundary := stateClosure }
  change ∀ entry ∈ NativeDecoder.ProgramRows.programOf .reduced initial text, _
  rw [entries]
  exact text_caller_code NativeDecoder.ProgramRows.Config.reduced.fields text programSetup.size

end Airbender.Compiler.MachineTargets.Proofs
