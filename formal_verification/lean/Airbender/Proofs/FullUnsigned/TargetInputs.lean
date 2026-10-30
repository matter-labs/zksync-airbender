import Airbender.Proofs.Reduced.TargetInputs

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

/-- Full unsigned public text constructs the complete six-family stream registry. -/
theorem unrolled_full_ordinary_image {initial : State} {text : List (BitVec 32)}
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    programImageRunWith AddSub.Modular.External.decoderFields initial
      ((NativeDecoder.ProgramRows.programOf .fullUnsigned initial text).map ProgramEntry.pc) =
        some (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text) :=
  NativeDecoder.ProgramRows.Proofs.program_image .fullUnsigned initial text image size

/-- The standard full unsigned filter retains exact native caller metadata. -/
theorem unrolled_full_caller_metadata {instruction : SailRV32.instruction}
    {data : DecoderData Delegation.Family}
    (fields : FullUnsigned.standardDecoderFields instruction = some data) :
    Delegation.Caller.decoderFields instruction = some data ∧ FullUnsigned.standardCall data.family := by
  unfold FullUnsigned.standardDecoderFields at fields
  cases native : Delegation.Caller.decoderFields instruction with
  | none => simp [native] at fields
  | some found =>
    simp only [native, bind, Option.bind] at fields
    cases family : found.family <;> simp [family] at fields
    all_goals cases fields
    all_goals exact ⟨rfl, by simp [FullUnsigned.standardCall, family]⟩

/-- Standard full unsigned callers retain the original public Sail program image. -/
theorem unrolled_full_caller_image {initial : State} {text : List (BitVec 32)}
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    Delegation.Caller.programImage initial
      ((FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text).map ProgramEntry.pc) =
        some (FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text) := by
  apply Airbender.Compiler.PublicProgram.image_run
  intro entry member
  have source := text_caller_sources FullUnsigned.standardDecoderFields initial text image size entry member
  exact ⟨source.bytes, source.decoded, (unrolled_full_caller_metadata source.fields).1⟩

/-- The split registry reads the same public bytes with its exact CSR decoder. -/
theorem unrolled_full_split_caller_image {initial : State} {text : List (BitVec 32)}
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    programImageRunWith Keccak.Split.Caller.decoderFields initial
      ((FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text).map ProgramEntry.pc) =
        some (FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text) :=
  Airbender.Compiler.PublicProgram.image_run _
    (text_caller_sources Keccak.Split.Caller.decoderFields initial text image size)

/-- The native standalone boundary supplies full unsigned stream boot inputs. -/
theorem unrolled_full_initialization_inputs
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [Fact babyBearModulus.Prime]
    {initial : State} {text : List (BitVec 32)}
    {bundles : List UnifiedReduced.Caller.DelegationUse.Bundle}
    {splitBundles : List Keccak.Split.Bundle}
    {trace : PooledTrace babyBearModulus}
    (geometry : Initialization.Geometry Initialization.standalone.layout)
    (windows : Initialization.Windows Initialization.standalone.layout)
    {E : Type} [CommRing E] (embed : F →+* E)
    (additive : E) (weights : Fin 6 → E) (boundary : InitializationWitness E)
    (terminalRegisters : List (MemoryToken babyBearModulus))
    {capacity : Nat} {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List F)}
    (profile : PublicProfile initial (Initialization.cells geometry windows))
    (programSetup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (loads : NoDiscardedLoads (FullUnsigned.Program.ofText initial text bundles splitBundles).ordinary)
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
      (FullUnsigned.Program.ofText initial text bundles splitBundles).ordinary
      AddSub.Modular.External.decoderFields := by
  have seed : trace.initialMemory = ROMView.nativeBootImage (Initialization.cells geometry windows) :=
    initializationBoundary.1.trans (Initialization.Proofs.computed_seed trace
      Initialization.standalone.layout geometry windows embed additive weights boundary.raw terminalRegisters)
  have entries : NativeDecoder.ProgramRows.programOf .fullUnsigned initial text =
      FullUnsigned.entriesWith NativeDecoder.ProgramRows.Config.fullUnsigned.fields text := rfl
  refine {
    registers := ExternalBoundary.Initialization.Proofs.all_registers (windows.selection geometry)
    ordinary := profile.ordinary
    configuration := profile.configuration
    landingPadDisabled := profile.landingPadDisabled
    code := ?_
    loads := loads
    distinct := ExternalBoundary.Initialization.Proofs.cells_distinct (windows.selection geometry)
    aligned := ExternalBoundary.Initialization.Proofs.aligned (windows.selection geometry)
    programImage := ⟨_, unrolled_full_ordinary_image programSetup.image programSetup.size⟩
    profile := profile.bootProfile
    seed := seed
    initialBoundary := initialBoundary
    physicalImage := wordSetup
    subwordSetup := subwordSetup
    verifierBoundary := stateClosure }
  change ∀ entry ∈ NativeDecoder.ProgramRows.programOf .fullUnsigned initial text, _
  rw [entries]
  exact text_caller_code NativeDecoder.ProgramRows.Config.fullUnsigned.fields text programSetup.size

end Airbender.Compiler.MachineTargets.Proofs
