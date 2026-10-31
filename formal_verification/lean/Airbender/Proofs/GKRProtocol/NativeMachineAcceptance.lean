import Airbender.Review.Compiler.NativeMachineArguments
import Airbender.Proofs.GKRProtocol.ProgramPublicConstraints
import Airbender.Proofs.GKRProtocol.ProgramUnifiedConstraints

namespace Airbender.Compiler.MachineTargets
open Airbender.Trace Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Native public-program rows close CPU acceptance and decoder matching
for both unrolled targets. All exact matching boundaries keep their meaning. -/
theorem unrolled_acceptance_from_native
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    {certificates : List (PooledExecution.ProgramLogicalRowCertificate
      (unrolledProgramLookupRows initial columns))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (arguments : UnrolledNativeArguments initial columns certificates trace workers extraSteps extraRequests)
    {cells : List Cell} (domain : ROMNative.WordFullPublic.CoversROM cells)
    (wordSetup : ∃ image, initialImage initial cells = some image ∧
      trace.rom.wordMemory = ROM.table cells image)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0)) :
    UnrolledAcceptance trace workers extraSteps extraRequests ∧
      UnrolledDecoderExactLookup trace masks columns := by
  obtain ⟨image, physical, wordEq⟩ := wordSetup
  have initialBound : trace.initial.word.lo < 65536 := by
    rw [initialBoundary]
    exact of_decide_eq_true rfl
  have asPublic : trace.rom = (⟨ROM.table cells image,
      Verification.subwordTable (ROM.words initial)⟩ : PooledSetup babyBearModulus) := by
    calc
      trace.rom = ⟨trace.rom.wordMemory, trace.rom.subwordMemory⟩ := rfl
      _ = _ := by rw [wordEq, subwordSetup]
  have equations := PooledExecution.program_row_constraints_from_native setup physical domain
    certificates trace arguments.rows arguments.states initialBound
  have cpu : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
    simpa only [asPublic] using equations
  have active : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1 := by
    intro row member
    have certified : row ∈ certificates.map PooledExecution.ProgramLogicalRowCertificate.row := arguments.rows ▸ member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp certified
    exact cert.row_active
  exact ⟨⟨cpu, active, arguments.workerEquations, arguments.workerActive,
      arguments.states, arguments.requests, arguments.ram⟩,
    PooledExecution.program_decoder_exact_lookup_from_native setup certificates trace
      arguments.rows arguments.states initialBound⟩

/-- Native unified rows close the target's CPU and public decoder premises. -/
theorem unified_acceptance_from_native
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    {certificates : List (UnifiedExecution.ProgramLogicalRowCertificate
      (unifiedLookupRows initial columns))}
    {trace : UnifiedTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (arguments : UnifiedNativeArguments initial columns certificates trace workers)
    (romSetup : trace.rom = UnifiedReduced.Setup.table initial)
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0)) :
    UnifiedAcceptance trace workers ∧ UnifiedDecoderExactLookup trace mask columns := by
  have initialBound : trace.initial.word.lo < 65536 := by
    rw [initialBoundary]
    exact of_decide_eq_true rfl
  have equations := UnifiedExecution.program_row_constraints_from_native setup certificates trace
    arguments.rows arguments.states initialBound
  have cpu : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
    simpa only [romSetup] using equations
  have active : ∀ row ∈ trace.rows, row.assignment row.columns.execute = 1 := by
    intro row member
    have certified : row ∈ certificates.map UnifiedExecution.ProgramLogicalRowCertificate.row := arguments.rows ▸ member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp certified
    exact cert.row_active
  exact ⟨⟨cpu, active, arguments.workerEquations, arguments.workerActive,
      arguments.states, arguments.requests, arguments.ram⟩,
    UnifiedExecution.decoder_exact_lookup_from_native setup certificates trace
      arguments.rows arguments.states initialBound⟩

end Airbender.Compiler.MachineTargets
