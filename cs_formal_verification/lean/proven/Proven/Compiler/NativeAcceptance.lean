module
public import Proven.Compiler.Clock.AddSub
public import Proven.Compiler.Decoder.AddSub
public import Proven.Compiler.Clock.JumpBranch
public import Proven.Compiler.Decoder.JumpBranch
public import Proven.Compiler.Clock.MulDiv
public import Proven.Compiler.Decoder.MulDiv
public import Proven.Compiler.Clock.ShiftBinop
public import Proven.Compiler.Decoder.ShiftBinop
public import Proven.Compiler.Clock.WordMemory
public import Proven.Compiler.Decoder.WordMemory
public import Proven.Compiler.Clock.SubwordMemory
public import Proven.Compiler.Decoder.SubwordMemory
public import Proven.Compiler.Clock.Unified
public import Proven.Compiler.Decoder.Unified
public import Proven.Compiler.PCLow
public import Proven.Compiler.ProgramMembership

@[expose] public section
namespace Airbender.Compiler.NativeAcceptance
open Airbender Trace NativeArithmetic NativePublicSetup Trace.Machine
set_option warningAsError true
set_option maxRecDepth 65536

/-- Each physical CPU certificate supplies all retained clock constraints. -/
theorem pooled_constraints {initial : RV.State} {program : List RVMachineProgramEntry}
    {tables : ProgramLookupRows} (bound : Bound initial program tables)
    (cells : List Cell) (covers : CoversROM cells) (cert : ProgramLogicalRowCertificate tables) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (⟨ROM.table cells (romImageRV initial cells),
        Verification.subwordTable (ROM.wordsRV initial)⟩ : PooledSetup babyBearModulus)) := by
  rcases cert with ⟨⟨family, assignment⟩, physical, arithmetic, placement, lookups, active⟩
  rw [bound.binding] at lookups
  cases family with
  | addSub => exact NativeClock.AddSub.logical initial program physical assignment arithmetic placement lookups
  | jumpBranchSlt => exact NativeClock.JumpBranch.logical initial program physical assignment arithmetic placement lookups
  | mulDiv => exact NativeClock.MulDiv.logical initial program physical assignment arithmetic placement lookups
  | shiftBinop => exact NativeClock.ShiftBinop.logical initial program bound physical assignment arithmetic placement lookups
  | wordMemory => exact NativeClock.WordMemory.logical initial program bound cells covers physical assignment arithmetic placement lookups
  | subwordMemory => exact NativeClock.SubwordMemory.logical initial program bound physical assignment arithmetic placement lookups

/-- The unified physical certificate supplies every retained clock constraint. -/
theorem unified_constraints {initial : RV.State} {program : List RVMachineProgramEntry}
    {tables : ProgramLookupRows} (bound : Bound initial program tables)
    (cert : UnifiedLogicalRowCertificate tables) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (UnifiedReduced.Setup.tableRV initial)) := by
  rcases cert with ⟨⟨family, assignment⟩, physical, arithmetic, placement, lookups, active⟩
  rw [bound.binding] at lookups
  cases family
  exact NativeClock.Unified.logical initial program bound physical assignment arithmetic placement lookups

/-- Exact native decoder matching supplies the complete public program entry. -/
theorem pooled_decoded {initial : RV.State} {program : List RVMachineProgramEntry}
    {tables : ProgramLookupRows} (bound : Bound initial program tables)
    (cert : ProgramLogicalRowCertificate tables) (typed : cert.row.decoderQuery[0].val < 65536) :
    Decoded (.pooled cert.row.family) cert.row.decoderQuery program := by
  rcases cert with ⟨⟨family, assignment⟩, physical, arithmetic, placement, lookups, active⟩
  rw [bound.binding] at lookups
  cases family with
  | addSub =>
    apply NativePublicSetup.Proofs.decoded bound (.pooled .addSub) _ typed ?_
      (NativeDecoder.AddSub.member initial program physical assignment arithmetic placement active lookups)
    intro _
    rfl
  | jumpBranchSlt =>
    apply NativePublicSetup.Proofs.decoded bound (.pooled .jumpBranchSlt) _ typed ?_
      (NativeDecoder.JumpBranch.member initial program physical assignment arithmetic placement active lookups)
    intro absent
    simp [NativePublicSetup.Metadata.hasFunct3] at absent
  | mulDiv =>
    apply NativePublicSetup.Proofs.decoded bound (.pooled .mulDiv) _ typed ?_
      (NativeDecoder.MulDiv.member initial program physical assignment arithmetic placement active lookups)
    intro _
    rfl
  | shiftBinop =>
    apply NativePublicSetup.Proofs.decoded bound (.pooled .shiftBinop) _ typed ?_
      (NativeDecoder.ShiftBinop.member initial program physical assignment arithmetic placement active lookups)
    intro absent
    simp [NativePublicSetup.Metadata.hasFunct3] at absent
  | wordMemory =>
    apply NativePublicSetup.Proofs.decoded bound (.pooled .wordMemory) _ typed ?_
      (NativeDecoder.WordMemory.member initial program physical assignment arithmetic placement active lookups)
    intro _
    rfl
  | subwordMemory =>
    apply NativePublicSetup.Proofs.decoded bound (.pooled .subwordMemory) _ typed ?_
      (NativeDecoder.SubwordMemory.member initial program physical assignment arithmetic placement active lookups)
    intro _
    rfl

theorem unified_decoded {initial : RV.State} {program : List RVMachineProgramEntry}
    {tables : ProgramLookupRows} (bound : Bound initial program tables)
    (cert : UnifiedLogicalRowCertificate tables) (typed : cert.row.decoderQuery[0].val < 65536) :
    Decoded .unified cert.row.decoderQuery program := by
  rcases cert with ⟨⟨family, assignment⟩, physical, arithmetic, placement, lookups, active⟩
  rw [bound.binding] at lookups
  cases family
  apply NativePublicSetup.Proofs.decoded bound .unified _ typed ?_
    (NativeDecoder.Unified.member initial program physical assignment arithmetic placement active lookups)
  intro absent
  simp [NativePublicSetup.Metadata.hasFunct3] at absent

/-- The exact state permutation carries independently ranged output limbs to decoder incoming. -/
theorem incoming_low {Kind : Type} [CircuitLayout Kind] (trace : Data babyBearModulus Kind)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start))
    (initial : trace.initial.word.lo < 65536)
    (outputs : ∀ row ∈ trace.rows, row.finish.word.lo < 65536) :
    ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536 := by
  intro row member
  have incoming : row.start.word.lo < 65536 := by
    have matched := states.mem_iff.mpr
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
    rcases List.mem_cons.mp matched with same | previous
    · exact same ▸ initial
    · obtain ⟨previous, present, equal⟩ := List.mem_map.mp previous
      exact equal ▸ outputs previous present
  exact incoming

/-- Physical certificates derive CPU acceptance and decoder authentication for an unrolled trace. -/
theorem unrolled {initial : RV.State} {program : List RVMachineProgramEntry}
    {tables : ProgramLookupRows} (bound : Bound initial program tables)
    (cells : List Cell) (covers : CoversROM cells)
    (certificates : List (ProgramLogicalRowCertificate tables))
    (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (arguments : UnrolledNativeArguments tables certificates trace workers)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial))
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0)) :
    UnrolledAcceptance trace workers program := by
  have asPublic : trace.rom = (⟨ROM.table cells (romImageRV initial cells),
      Verification.subwordTable (ROM.wordsRV initial)⟩ : PooledSetup babyBearModulus) := by
    cases rom : trace.rom
    simp_all
  have constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
    intro row member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (arguments.rows ▸ member)
    rw [asPublic]
    exact pooled_constraints bound cells covers cert
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo < 65536 := by
    intro row member
    exact Trace.NativeDecoder.Proofs.pooled_final_pc_low (by decide +kernel) row trace.rom (constraints row member)
  have incoming := incoming_low trace arguments.states (by rw [initialBoundary]; decide +kernel) outputs
  refine ⟨arguments.toWorkersAccepted, constraints, ?_, arguments.states, ?_, arguments.requests, arguments.memory⟩
  · intro row member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (arguments.rows ▸ member)
    exact cert.active
  · intro row member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (arguments.rows ▸ member)
    exact pooled_decoded bound cert (incoming cert.row member)

/-- Physical unified certificates close CPU acceptance and public decoder authentication. -/
theorem unified {initial : RV.State} {program : List RVMachineProgramEntry}
    {tables : ProgramLookupRows} (bound : Bound initial program tables)
    (certificates : List (UnifiedLogicalRowCertificate tables))
    (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus)
    (arguments : UnifiedNativeArguments tables certificates trace workers)
    (setup : trace.rom = UnifiedReduced.Setup.tableRV initial)
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0)) :
    UnifiedAcceptance trace workers program := by
  have constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
    intro row member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (arguments.rows ▸ member)
    rw [setup]
    exact unified_constraints bound cert
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo < 65536 := by
    intro row member
    cases row with
    | mk family assignment =>
      cases family
      have core := Verification.holds_of_sublist (constraints ⟨.machine, assignment⟩ member)
        (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom)
          UnifiedReduced.importedConstraintsTimestampLookups)
      exact (UnifiedReduced.Proofs.pc_bounds core).1
  have incoming := incoming_low trace arguments.states (by rw [initialBoundary]; decide +kernel) outputs
  refine ⟨arguments.toWorkersAccepted, constraints, ?_, arguments.states, ?_, arguments.requests, arguments.memory⟩
  · intro row member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (arguments.rows ▸ member)
    exact cert.active
  · intro row member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (arguments.rows ▸ member)
    exact unified_decoded bound cert (incoming cert.row member)

end Airbender.Compiler.NativeAcceptance
