import Airbender.Review.Trace.Families.ReducedMachine.SupportedExecution
import Airbender.Review.Trace.Families.ReducedMachine.SupportedValues

namespace Tests.NativeReducedSupportedExecution
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Empty rows still bind the actual native/public PC and initial clock. No
    instruction row or complete positive117-equation row is claimed here. -/
private def before (pc : BitVec 32) : State :=
  { (default : State) with regs := Std.ExtDHashMap.emptyWithCapacity.insert .PC pc }

private def emptyTrace (pc : BitVec 32) : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeFixed.table
  initial := PCState.boundary pc (4,0)
  terminal := PCState.boundary pc (4,0)
  initialMemory := []
  terminalMemory := []

private def emptySetup : SparseDecoderSetup SupportedMode := ⟨[],1⟩

private theorem public_inputs (pc : BitVec 32) :
    ImageBoundary (fixedData (emptyTrace pc)) (before pc) [] := by
  refine ⟨by simp,rfl,?_⟩
  have read : run (SailRV32.Functions.get_arch_pc ()) (before pc) = .ok pc (before pc) := by
    apply read_register
    simp [before]
  change initialState (before pc) (4,0) = some (PCState.boundary pc (4,0))
  simp only [initialState,read]

private theorem accepted (pc : BitVec 32) : Accepted (fixedData (emptyTrace pc)) := by
  constructor
  · intro row present; simp [fixedData,emptyTrace] at present
  · intro row present; simp [fixedData,emptyTrace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _

private theorem decoded (pc : BitVec 32) :
    SupportedDecodedTrace (fixedData (emptyTrace pc)) emptySetup := by
  intro row present; simp [fixedData,emptyTrace] at present

/-- A concrete actual-native zero-row trace passes the complete public execution
    boundary for every RV32 PC, with no assumed terminal bound or Sail states. -/
theorem empty_execution (pc : BitVec 32) :
    (emptyTrace pc).terminal.word.Bounded ∧
    Realizes (StepWith supportedDecoderFields registerClause emptySetup.program)
      (fixedData (emptyTrace pc)) (before pc) [] := by
  exact public_supported_execution (count := 0) (logCapacity := 0) rfl
    (public_inputs pc) (accepted pc) (decoded pc) (by
      rintro ⟨entry,member,_⟩
      simp [SparseDecoderSetup.program] at member) (by simp)

/-- The actual terminal PC reader is recovered even at the top RV32 word; an
    empty path does not fabricate PC+4 or require an instruction alignment input. -/
theorem empty_top_endpoint : ∃ after : State,
    Relation.ReflTransGen (StepWith supportedDecoderFields registerClause emptySetup.program)
      (before 0xffffffff) after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (0xffffffff : BitVec 32) after := by
  obtain ⟨after,steps,pc,_⟩ := (empty_execution 0xffffffff).2
  have canonical : (emptyTrace 0xffffffff).terminal.word.toBitVec = 0xffffffff := by decide +kernel
  change run (SailRV32.Functions.get_arch_pc ()) after =
    .ok (emptyTrace 0xffffffff).terminal.word.toBitVec after at pc
  rw [canonical] at pc
  exact ⟨after,steps,pc⟩

/-- Common initialized induction rejects an oversized actual source read even
    when accepted rows interleave the supported profiles. No row range input. -/
theorem oversized_source_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (decoded : SupportedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows)
    (oversized : limbBase ≤ (row.assignment 35).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have ranges := (public_supported_value_bounds image inputs accepted decoded).1 row present
  cases row with
  | mk family w =>
    cases family
    have bound := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at bound
    exact Nat.not_le_of_gt bound.1 oversized

/-- Original public initialization and actual mixed native matching derive x0
    writes through one common induction, retaining discarded/readonly accesses. -/
theorem nonzero_x0_event_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (decoded : SupportedDecodedTrace (fixedData trace) setup)
    (event : MemoryAccess) (present : event ∈ (fixedData trace).nativeEvents)
    (address : event.2.1 = (Cell.register 0).addressCode)
    (nonzero : memoryWord event.2.2.2 ≠ 0) : ¬ Accepted (fixedData trace) := by
  intro accepted
  exact nonzero (NativeSupportedRegisterProofs.native_zero_writes image accepted
    (Trace.Proofs.image_clock_boundary (by decide) inputs) inputs.image decoded event present address)

/-- The full fetched theorem derives the terminal PC bound without a supplied
    local successor, intermediate Sail state or per-row profile answer. -/
theorem oversized_terminal_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (decoded : SupportedDecodedTrace (fixedData trace) setup)
    (isa : SupportedISA setup initial)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (oversized : limbBase ≤ trace.terminal.word.hi) :
    ¬ Accepted (fixedData trace) := by
  intro accepted
  exact Nat.not_le_of_gt (public_supported_execution image inputs accepted decoded isa aligned).1.2 oversized

end Tests.NativeReducedSupportedExecution
