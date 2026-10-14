import Tests.Comparison
import Airbender.Proofs.JumpBranchSlt.Claims
import Tests.JumpHistory
import Airbender.Proofs.JumpBranchSlt.ComparisonExecution

namespace Tests.ComparisonTrace
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

-- All four comparisons of zero with -1, with rd aliasing the selected source.
private def assignment (signed immediate : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then 4 else if i = 18 then 8
  else if i = 28 || i = 29 then (if immediate then 0 else 65535)
  else if i = 32 then (if immediate then 4 else 5)
  else if i = 49 || i = 50 || i = 51 then 1
  else Comparison.edgeRow signed immediate false i

private def entry (signed immediate : Bool) : JumpBranchSlt.ProgramEntry :=
  ⟨0, if immediate then (if signed then 0xfff0a093 else 0xfff0b093)
      else (if signed then 0x0020a133 else 0x0020b133),
    if immediate then .ITYPE (0xfff, .Regidx 1, .Regidx 1, if signed then .SLTI else .SLTIU)
      else .RTYPE (.Regidx 2, .Regidx 1, .Regidx 2, if signed then .SLT else .SLTU),
    ⟨(), 1, if immediate then 0 else 2, if immediate then 1 else 2,
      if immediate then ⟨65535, 65535⟩ else ⟨0, 0⟩, 4, if signed then 2 else 3⟩⟩

private def before (signed immediate : Bool) : State :=
  wordWriteState { (default : State) with regs :=
    ((Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (0 : BitVec 32) |>.insert .x2 (0xffffffff : BitVec 32) |>.insert .PC 0) }
    0 (entry signed immediate).bits

private def cells : List Cell := [.register 0, .register 1, .register 2]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0,
    Cell.initialToken (.register 2) 0xffffffff]
private def row (signed immediate : Bool) : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, assignment signed immediate⟩

private def token (index clock value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (clock, 0), value⟩

private def trace (signed immediate : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row signed immediate]
  rom := rom
  initial := (row signed immediate).start
  terminal := (row signed immediate).finish
  initialMemory := seed
  terminalMemory := if immediate then
    [token 0 5 0, token 1 6 (Nat.pair (if signed then 0 else 1) 0), token 2 0 (Nat.pair 65535 65535)]
    else [token 0 0 0, token 1 4 0, token 2 6 (Nat.pair (if signed then 0 else 1) 0)]

private theorem constraints (signed immediate : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment signed immediate)) JumpBranchSlt.clockConstraints := by
  apply Verification.holds_append (left := JumpBranchSlt.importedConstraints)
    (right := JumpBranchSlt.importedConstraintsTimestampLookups)
  · have core := Comparison.edgeSatisfies signed immediate false
    cases signed <;> cases immediate <;>
      simpa [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Lookup.Contains, Vector.map, Expression.eval, Verification.environment, assignment, Comparison.edgeRow,
        Verification.range16, Verification.pairLookup, Verification.jumpCleanup,
        show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide] using core
  · cases signed <;> cases immediate <;>
      simp [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment, Comparison.edgeRow]
    all_goals decide

private theorem accepted (signed immediate : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : Accepted (trace signed immediate rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact constraints signed immediate
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    cases signed <;> cases immediate <;> rfl
  · exact List.Perm.swap _ _ []
  · cases signed <;> cases immediate <;>
      dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
        JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns]
    all_goals decide

private theorem boundary (signed immediate : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace signed immediate rom) := by
  constructor
  · cases signed <;> cases immediate <;> change 4 < timestampBase ∧ 0 < timestampBase
    all_goals constructor <;> decide
  · cases signed <;> cases immediate <;> change 4 % 4 = 0
    all_goals decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private theorem image (signed immediate : Bool) : initialImage (before signed immediate) cells = some seed := by
  have zero : (Cell.register 0).read (before signed immediate) = .ok 0 (before signed immediate) := rfl
  have one : (Cell.register 1).read (before signed immediate) = .ok 0 (before signed immediate) := by
    apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read (before signed immediate) = .ok 0xffffffff (before signed immediate) := by
    apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, zero, one, two]
  rfl

private theorem program_image (signed immediate : Bool) :
    JumpBranchSlt.programImage (before signed immediate) [0] = some [entry signed immediate] := by
  have bytes : (Cell.ram 0).read (before signed immediate) =
      .ok (entry signed immediate).bits (before signed immediate) := written_word_read _ 0 _
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind]
  cases signed <;> cases immediate <;> rfl

private theorem query (signed immediate : Bool) :
    JumpBranchSlt.decoderQuery (assignment signed immediate) = (entry signed immediate).query := by
  cases signed <;> cases immediate <;> decide

private theorem decoded (signed immediate : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.Decoded (trace signed immediate rom) [entry signed immediate] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  cases signed <;> cases immediate <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, query _ _⟩

/-- Actual public bytes, native matching and initialization derive every read.
    Signed and unsigned comparisons, including both immediate variants, reach
    the actual aliased native after-state through Sail's normal retirement. -/
theorem actual_comparison_retirement (signed immediate : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      initialState (retiredState (before signed immediate) 0) (4, 0) =
        some (trace signed immediate rom).initial ∧
      run (normalStep (if immediate then
        SailRV32.Functions.execute_ITYPE 0xfff (.Regidx 1) (.Regidx 1) (if signed then .SLTI else .SLTIU)
        else SailRV32.Functions.execute_RTYPE (.Regidx 2) (.Regidx 1) (.Regidx 2) (if signed then .SLT else .SLTU)))
        (retiredState (before signed immediate) 0) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after 4) ∧
      run (SailRV32.Functions.rX_bits (.Regidx (if immediate then 1 else 2))) after =
        .ok (if signed then 0 else 1) after := by
  obtain ⟨history, rows, after, _, permutation, _, execution, _⟩ :=
    JumpBranchSlt.Proofs.decoded_native_history (by decide) (by decide)
      (accepted signed immediate rom) (boundary signed immediate rom) (image signed immediate)
      (by decide)
      (by intro cell member; simp [cells] at member; rcases member with rfl | rfl | rfl <;> trivial)
      (program_image signed immediate) (decoded signed immediate rom)
  have single : rows = [row signed immediate] := by
    simpa only [trace] using List.perm_singleton.mp permutation
  subst rows
  have native : SailHistory cells
      (JumpBranchSlt.Proofs.nativeEvents (trace signed immediate rom).memoryEpoch
        (assignment signed immediate)).reverse (before signed immediate) after := by
    simpa [Trace.rowEvents, row, Row.ports, Row.columns] using execution
  have checked := JumpBranchSlt.Proofs.comparison_rebased_step (by decide) (by decide)
    (accepted signed immediate rom) (boundary signed immediate rom) (image signed immediate)
    (program_image signed immediate) (decoded signed immediate rom)
    (by cases signed <;> cases immediate <;> change (⟨4, 0⟩ : Word).Bounded
        all_goals constructor <;> decide)
    (by cases signed <;> cases immediate <;> change 0 % 4 = 0
        all_goals decide)
    (by simp [trace, row]) (by simp) (query signed immediate)
    (if signed then (if immediate then .slti else .slt) else (if immediate then .sltiu else .sltu))
    0xfff 1 2 (if immediate then 1 else 2)
    (by cases signed <;> cases immediate <;> rfl) native
  have written := JumpBranchSlt.Proofs.register_write (by decide)
    (trace signed immediate rom).memoryEpoch (query signed immediate) native
  have code : memoryWord (JumpBranchSlt.importedConstraintsMemoryPorts[2].writeCode
      (assignment signed immediate)) = (if signed then 0 else 1 : BitVec 32) := by
    cases signed <;> cases immediate <;>
      norm_num [memoryWord, JumpBranchSlt.importedConstraintsMemoryPorts,
        MemoryPort.writeCode, pairCode, assignment, Comparison.edgeRow,
        Word.toBitVec, Word.value, ZMod.val_ofNat, babyBearModulus]
    all_goals rfl
  rw [code] at written
  change run (SailRV32.Functions.wX_bits (.Regidx (if immediate then 1 else 2))
    (if signed then 0 else 1)) (before signed immediate) = .ok () after at written
  obtain ⟨actual, write, _, read⟩ := gpr_write_readback (if immediate then 1 else 2)
    (if signed then 0 else 1) (before signed immediate)
    (by cases immediate <;> simp)
  have same := (EStateM.Result.ok.inj (written.symm.trans write)).2
  subst actual
  refine ⟨after, ?_, ?_, read⟩
  · rw [initialState, Proofs.retired_state_pc (before signed immediate) 0]
    cases signed <;> cases immediate <;> rfl
  · cases signed <;> cases immediate <;>
      norm_num [JumpBranchSlt.Comparison.execution, JumpBranchSlt.Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, assignment, Comparison.edgeRow,
        Word.toBitVec, Word.value, limbBase, ZMod.val_ofNat, babyBearModulus] at checked ⊢
    all_goals exact checked

private def pooledProgram (signed immediate : Bool) : List PooledProgramEntry :=
  [(entry signed immediate).mapFamily (fun _ => .jumpBranchSlt)]

private def pooled (signed immediate : Bool) : PooledTrace babyBearModulus where
  rows := [⟨.jumpBranchSlt, (row signed immediate).assignment⟩]
  rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words (before signed immediate))⟩
  initial := (trace signed immediate (ROM.table cells seed)).initial
  terminal := (trace signed immediate (ROM.table cells seed)).terminal
  initialMemory := seed
  terminalMemory := (trace signed immediate (ROM.table cells seed)).terminalMemory

private theorem pooledAccepted (signed immediate : Bool) : Accepted (pooled signed immediate) := by
  constructor
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    exact constraints signed immediate
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    cases signed <;> cases immediate <;> rfl
  · exact (accepted signed immediate (ROM.table cells seed)).states
  · exact (accepted signed immediate (ROM.table cells seed)).memory

private theorem pooledImage (signed immediate : Bool) :
    pooledProgramImage (before signed immediate) [0] = some (pooledProgram signed immediate) := by
  have source := Proofs.program_sources (program_image signed immediate) (entry signed immediate) (by simp)
  have bytes := source.bytes
  change (Cell.ram 0).read (before signed immediate) = .ok (entry signed immediate).bits (before signed immediate) at bytes
  simp only [pooledProgramImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, source.decoded, bind, Option.bind]
  cases signed <;> cases immediate <;> rfl

private theorem pooledDecoded (signed immediate : Bool) : PooledDecoded (pooled signed immediate) (pooledProgram signed immediate) := by
  intro actual member
  simp only [pooled, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _ = _
  exact ⟨0, by cases signed <;> cases immediate <;> decide⟩

private theorem pooledInputs (signed immediate : Bool) :
    NativeInputs pooledDecoderFields (pooled signed immediate) (before signed immediate) cells (pooledProgram signed immediate) := by
  refine ⟨by decide, ?_, image signed immediate, ?_, ⟨[0], pooledImage signed immediate⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl <;> trivial
  · refine ⟨(4, 0), ?_⟩
    have read : run (SailRV32.Functions.get_arch_pc ()) (before signed immediate) = .ok 0 (before signed immediate) := by
      apply read_register
      simp [before, wordWriteState]
    rw [initialState, read]
    cases signed <;> cases immediate <;> rfl
  · exact ⟨(boundary signed immediate (ROM.table cells seed)).initial,
      (boundary signed immediate (ROM.table cells seed)).aligned,
      (boundary signed immediate (ROM.table cells seed)).memory⟩

private theorem sharedInputs (signed immediate : Bool) :
    JumpBranchSlt.TraceInputs (pooled signed immediate) (before signed immediate) cells (pooledProgram signed immediate) := by
  refine ⟨⟨pooledInputs signed immediate, rfl, rfl⟩, ?_, ?_⟩
  · intro actual member
    simp only [pooledProgram, List.mem_singleton] at member
    subst actual
    cases signed <;> cases immediate <;> decide
  · refine ⟨VerifierBoundary.boot ⟨4, (8, 0)⟩, ?_⟩
    apply VerifierBoundary.Proofs.binding_of_endpoints
    · cases signed <;> cases immediate <;> rfl
    · cases signed <;> cases immediate <;> rfl
    · exact (pooledAccepted signed immediate).states

theorem per_circuit_comparison_soundness (signed immediate : Bool) :
    ∃ input : JumpBranchSlt.Comparison.Input,
      (JumpBranchSlt.Comparison.circuitModel (pooled signed immediate) (before signed immediate) cells (pooledProgram signed immediate)).relation
        input (⟨⟨if signed then 0 else 1, 0⟩, ⟨4, 0⟩⟩ : Output) ((row signed immediate).assignment) ∧
      JumpBranchSlt.Comparison.InterfaceAssumptions (pooled signed immediate) (before signed immediate) cells (pooledProgram signed immediate) ∧
      JumpBranchSlt.Comparison.spec input (⟨⟨if signed then 0 else 1, 0⟩, ⟨4, 0⟩⟩ : Output) := by
  have member : (⟨.jumpBranchSlt, (row signed immediate).assignment⟩ : Row babyBearModulus PooledFamily) ∈
      (pooled signed immediate).rows := by simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    (pooledAccepted signed immediate) (pooledInputs signed immediate).clocks (pooledInputs signed immediate).image
    (pooledInputs signed immediate).distinct (pooledInputs signed immediate).aligned
    (pooledImage signed immediate) (pooledDecoded signed immediate) member
  let input : JumpBranchSlt.Comparison.Input := ⟨if signed then (if immediate then .slti else .slt) else (if immediate then .sltiu else .sltu),
      ⟨0, 0⟩, ⟨65535, 65535⟩, ⟨0, 0⟩, .Regidx 1,
      .Regidx (if immediate then 0 else 2), .Regidx (if immediate then 1 else 2), 0xfff, current⟩
  let output : Output := ⟨⟨if signed then 0 else 1, 0⟩, ⟨4, 0⟩⟩
  have mapping : JumpBranchSlt.Comparison.TraceMapping (pooled signed immediate) (before signed immediate) cells
      (pooledProgram signed immediate) input output ((row signed immediate).assignment) := by
    refine ⟨?_, position, ?_⟩
    · constructor <;> cases signed <;> cases immediate <;> rfl
    · refine ⟨(entry signed immediate).mapFamily (fun _ => .jumpBranchSlt), by simp [pooledProgram], rfl, ?_, ?_⟩
      · cases signed <;> cases immediate <;> decide
      · cases signed <;> cases immediate <;> rfl
  have assumptions : JumpBranchSlt.Comparison.InterfaceAssumptions (pooled signed immediate) (before signed immediate) cells
      (pooledProgram signed immediate) := sharedInputs signed immediate
  have relation : (JumpBranchSlt.Comparison.circuitModel (pooled signed immediate) (before signed immediate) cells
      (pooledProgram signed immediate)).relation input output ((row signed immediate).assignment) :=
    ⟨⟨ pooledAccepted signed immediate, pooledDecoded signed immediate, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, JumpBranchSlt.Comparison.babyBear_soundness (pooled signed immediate)
    (before signed immediate) cells (pooledProgram signed immediate) assumptions input output _ relation⟩

theorem per_circuit_pc_alias_rejected (current : State) :
    ¬ JumpBranchSlt.Comparison.TraceMapping (pooled false false) (before false false) cells
      (pooledProgram false false)
      (⟨.sltu, ⟨0, 0⟩, ⟨65535, 65535⟩, ⟨babyBearModulus, 0⟩,
        .Regidx 1, .Regidx 2, .Regidx 2, 0xfff, current⟩ : JumpBranchSlt.Comparison.Input)
      ⟨⟨1, 0⟩, ⟨4, 0⟩⟩ (row false false).assignment := by
  intro mapping
  have impossible := mapping.words.pcLo
  change babyBearModulus = ((row false false).assignment 0).val at impossible
  have small := ZMod.val_lt ((row false false).assignment 0)
  omega

end Tests.ComparisonTrace
