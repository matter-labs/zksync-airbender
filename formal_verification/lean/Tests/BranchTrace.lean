import Tests.Branch
import Airbender.Proofs.JumpBranchSlt.Claims
import Tests.JumpHistory
import Airbender.Proofs.JumpBranchSlt.BranchExecution

namespace Tests.BranchTrace
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def opcode (tag : Fin 6) : SailRV32.bop :=
  match tag.val with
  | 0 => .BEQ | 1 => .BNE | 2 => .BLT | 3 => .BGE | 4 => .BLTU | _ => .BGEU

private def assignment (tag : Fin 6) (wrap : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then 4 else if i = 18 then 8
  else if i = 49 || i = 50 || i = 51 then 1
  else Branch.row tag wrap i

private def entry (tag : Fin 6) (wrap : Bool) : JumpBranchSlt.ProgramEntry :=
  ⟨(Branch.initial wrap).toBitVec,
    BitVec.ofNat 32 ((if wrap then 0x00208463 else 0xfe208ee3) + Branch.funct3 tag * 4096),
    .BTYPE ((if wrap then 8 else 8188), .Regidx 2, .Regidx 1, opcode tag),
    ⟨(), 1, 2, 0, Branch.offset wrap, 24, Branch.funct3 tag⟩⟩

private def before (tag : Fin 6) (wrap : Bool) : State :=
  wordWriteState { (default : State) with regs :=
    ((Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (0 : BitVec 32) |>.insert .x2 (0xffffffff : BitVec 32)
      |>.insert .PC (Branch.initial wrap).toBitVec |>.insert .misa (0 : BitVec 32)) }
    (Branch.initial wrap).toBitVec.toNat (entry tag wrap).bits

private def cells : List Cell := [.register 0, .register 1, .register 2]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0,
    Cell.initialToken (.register 2) 0xffffffff]
private def row (tag : Fin 6) (wrap : Bool) : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, assignment tag wrap⟩

private def trace (tag : Fin 6) (wrap : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row tag wrap]
  rom := rom
  initial := (row tag wrap).start
  terminal := (row tag wrap).finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 1).addressCode, (4, 0), 0⟩,
    ⟨(Cell.register 2).addressCode, (5, 0), Nat.pair 65535 65535⟩,
    ⟨(Cell.register 0).addressCode, (6, 0), 0⟩]

private theorem constraints (tag : Fin 6) (wrap : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment tag wrap)) JumpBranchSlt.clockConstraints := by
  apply Verification.holds_append (left := JumpBranchSlt.importedConstraints)
    (right := JumpBranchSlt.importedConstraintsTimestampLookups)
  · have core := Branch.satisfies tag wrap
    fin_cases tag <;> cases wrap <;>
      simpa [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Lookup.Contains, Vector.map, Expression.eval, Verification.environment, assignment,
        Branch.row, Verification.range16, Verification.pairLookup, Verification.jumpCleanup,
        show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide] using core
  · fin_cases tag <;> cases wrap <;>
      simp [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment, Branch.row]
    all_goals decide

private theorem accepted (tag : Fin 6) (wrap : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : Accepted (trace tag wrap rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact constraints tag wrap
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    fin_cases tag <;> cases wrap <;> rfl
  · exact List.Perm.swap _ _ []
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
      JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns]
    fin_cases tag <;> cases wrap <;> decide

private theorem boundary (tag : Fin 6) (wrap : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace tag wrap rom) := by
  constructor
  · fin_cases tag <;> cases wrap <;> change 4 < timestampBase ∧ 0 < timestampBase
    all_goals constructor <;> decide
  · fin_cases tag <;> cases wrap <;> change 4 % 4 = 0
    all_goals decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private theorem image (tag : Fin 6) (wrap : Bool) : initialImage (before tag wrap) cells = some seed := by
  have zero : (Cell.register 0).read (before tag wrap) = .ok 0 (before tag wrap) := rfl
  have one : (Cell.register 1).read (before tag wrap) = .ok 0 (before tag wrap) := by
    apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read (before tag wrap) = .ok 0xffffffff (before tag wrap) := by
    apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, zero, one, two]
  rfl

set_option maxHeartbeats 8000000 in
private theorem program_image (tag : Fin 6) (wrap : Bool) :
    JumpBranchSlt.programImage (before tag wrap) [(Branch.initial wrap).toBitVec] =
      some [entry tag wrap] := by
  have bytes : (Cell.ram (Branch.initial wrap).toBitVec).read (before tag wrap) =
      .ok (entry tag wrap).bits (before tag wrap) := written_word_read _ _ _
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind]
  fin_cases tag <;> cases wrap <;> rfl

private theorem query (tag : Fin 6) (wrap : Bool) :
    JumpBranchSlt.decoderQuery (assignment tag wrap) = (entry tag wrap).query := by
  fin_cases tag <;> cases wrap <;> decide

private theorem decoded (tag : Fin 6) (wrap : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.Decoded (trace tag wrap rom) [entry tag wrap] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  fin_cases tag <;> cases wrap <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, query _ _⟩

/-- Each of the six actual public branch encodings retires through its native
    history. Fixtures cover signed/unsigned disagreement, taken/not-taken paths,
    negative offsets and wraparound in both PC directions. -/
theorem actual_branch_retirement (tag : Fin 6) (wrap : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      initialState (retiredState (before tag wrap) (Branch.initial wrap).toBitVec) (4, 0) =
        some (trace tag wrap rom).initial ∧
      run (normalStep (SailRV32.Functions.execute_BTYPE (if wrap then 8 else 8188)
        (.Regidx 2) (.Regidx 1) (opcode tag)))
        (retiredState (before tag wrap) (Branch.initial wrap).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Branch.final tag wrap).toBitVec) ∧
      run (SailRV32.Functions.rX_bits (.Regidx 2)) after = .ok 0xffffffff after := by
  obtain ⟨history, rows, after, _, permutation, _, execution, _⟩ :=
    JumpBranchSlt.Proofs.decoded_native_history (by decide) (by decide)
      (accepted tag wrap rom) (boundary tag wrap rom) (image tag wrap)
      (by decide)
      (by intro cell member; simp [cells] at member; rcases member with rfl | rfl | rfl <;> trivial)
      (program_image tag wrap) (decoded tag wrap rom)
  have single : rows = [row tag wrap] := by
    simpa only [trace] using List.perm_singleton.mp permutation
  subst rows
  have native : SailHistory cells
      (JumpBranchSlt.Proofs.nativeEvents (trace tag wrap rom).memoryEpoch
        (assignment tag wrap)).reverse (before tag wrap) after := by
    simpa [Proofs.rowEvents, row, Row.ports, Row.columns] using execution
  have checked := JumpBranchSlt.Proofs.branch_rebased_step (by decide) (by decide)
    (accepted tag wrap rom) (boundary tag wrap rom) (image tag wrap)
    (program_image tag wrap) (decoded tag wrap rom)
    (by change (⟨(assignment tag wrap 16).val, (assignment tag wrap 17).val⟩ : Word).Bounded
        fin_cases tag <;> cases wrap <;> constructor <;> decide)
    (by change (assignment tag wrap 0).val % 4 = 0
        fin_cases tag <;> cases wrap <;> decide)
    (by simp [trace, row]) (by simp) (query tag wrap) (opcode tag)
    (if wrap then 8 else 8188) 1 2 rfl native (.nil _)
    (by refine ⟨0, ?_⟩; simp [before, wordWriteState])
  have written := JumpBranchSlt.Proofs.register_write (by decide)
    (trace tag wrap rom).memoryEpoch (query tag wrap) native
  change run (SailRV32.Functions.wX_bits (.Regidx 0) _) (before tag wrap) = .ok () after at written
  have same : before tag wrap = after := (EStateM.Result.ok.inj written).2
  subst after
  refine ⟨before tag wrap, ?_, ?_, ?_⟩
  · rw [initialState, Proofs.retired_state_pc]
    fin_cases tag <;> cases wrap <;> rfl
  · fin_cases tag <;> cases wrap <;>
      norm_num [assignment, Branch.row, Word.toBitVec, Word.value, limbBase,
        ZMod.val_ofNat, babyBearModulus] at checked ⊢
    all_goals exact checked
  · apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]

private def pooledProgram (tag : Fin 6) (wrap : Bool) : List PooledProgramEntry :=
  [(entry tag wrap).mapFamily (fun _ => .jumpBranchSlt)]

private def pooled (tag : Fin 6) (wrap : Bool) : PooledTrace babyBearModulus where
  rows := [⟨.jumpBranchSlt, (row tag wrap).assignment⟩]
  rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words (before tag wrap))⟩
  initial := (trace tag wrap (ROM.table cells seed)).initial
  terminal := (trace tag wrap (ROM.table cells seed)).terminal
  initialMemory := seed
  terminalMemory := (trace tag wrap (ROM.table cells seed)).terminalMemory

private theorem pooledAccepted (tag : Fin 6) (wrap : Bool) : Accepted (pooled tag wrap) := by
  constructor
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    exact constraints tag wrap
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    fin_cases tag <;> cases wrap <;> rfl
  · exact (accepted tag wrap (ROM.table cells seed)).states
  · exact (accepted tag wrap (ROM.table cells seed)).memory

private theorem pooledImage (tag : Fin 6) (wrap : Bool) :
    pooledProgramImage (before tag wrap) [(Branch.initial wrap).toBitVec] = some (pooledProgram tag wrap) := by
  have source := Proofs.program_sources (program_image tag wrap) (entry tag wrap) (by simp)
  have bytes := source.bytes
  change (Cell.ram (Branch.initial wrap).toBitVec).read (before tag wrap) = .ok (entry tag wrap).bits (before tag wrap) at bytes
  simp only [pooledProgramImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, source.decoded, bind, Option.bind]
  fin_cases tag <;> cases wrap <;> rfl

private theorem pooledDecoded (tag : Fin 6) (wrap : Bool) : PooledDecoded (pooled tag wrap) (pooledProgram tag wrap) := by
  intro actual member
  simp only [pooled, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _ = _
  exact ⟨0, by fin_cases tag <;> cases wrap <;> decide⟩

private theorem pooledInputs (tag : Fin 6) (wrap : Bool) :
    NativeInputs pooledDecoderFields (pooled tag wrap) (before tag wrap) cells (pooledProgram tag wrap) := by
  refine ⟨by decide, ?_, image tag wrap, ?_, ⟨[(Branch.initial wrap).toBitVec], pooledImage tag wrap⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl <;> trivial
  · refine ⟨(4, 0), ?_⟩
    have read : run (SailRV32.Functions.get_arch_pc ()) (before tag wrap) = .ok (Branch.initial wrap).toBitVec (before tag wrap) := by
      apply read_register
      simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    rw [initialState, read]
    fin_cases tag <;> cases wrap <;> rfl
  · exact ⟨(boundary tag wrap (ROM.table cells seed)).initial,
      (boundary tag wrap (ROM.table cells seed)).aligned,
      (boundary tag wrap (ROM.table cells seed)).memory⟩

private theorem sharedInputs (tag : Fin 6) (wrap : Bool) :
    JumpBranchSlt.TraceInputs (pooled tag wrap) (before tag wrap) cells (pooledProgram tag wrap) := by
  refine ⟨⟨pooledInputs tag wrap, rfl, rfl⟩, ?_, ?_⟩
  · intro actual member
    simp only [pooledProgram, List.mem_singleton] at member
    subst actual
    fin_cases tag <;> cases wrap <;> decide
  · fin_cases tag <;> cases wrap <;> constructor <;> decide

theorem per_circuit_branch_soundness (tag : Fin 6) (wrap : Bool) :
    ∃ input : JumpBranchSlt.Branch.Input,
      (JumpBranchSlt.Branch.circuitModel (pooled tag wrap) (before tag wrap) cells (pooledProgram tag wrap)).relation
        input (⟨⟨0, 0⟩, Branch.final tag wrap⟩ : Output) ((row tag wrap).assignment) ∧
      JumpBranchSlt.Branch.InterfaceAssumptions (pooled tag wrap) (before tag wrap) cells (pooledProgram tag wrap) ∧
      JumpBranchSlt.Branch.spec input (⟨⟨0, 0⟩, Branch.final tag wrap⟩ : Output) := by
  have member : (⟨.jumpBranchSlt, (row tag wrap).assignment⟩ : Row babyBearModulus PooledFamily) ∈
      (pooled tag wrap).rows := by simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    (pooledAccepted tag wrap) (pooledInputs tag wrap).clocks (pooledInputs tag wrap).image
    (pooledInputs tag wrap).distinct (pooledInputs tag wrap).aligned
    (pooledImage tag wrap) (pooledDecoded tag wrap) member
  let input : JumpBranchSlt.Branch.Input := ⟨opcode tag, ⟨0, 0⟩, ⟨65535, 65535⟩, Branch.offset wrap,
      Branch.initial wrap, .Regidx 1, .Regidx 2, (if wrap then 8 else 8188), current⟩
  let output : Output := ⟨⟨0, 0⟩, Branch.final tag wrap⟩
  have mapping : JumpBranchSlt.Branch.TraceMapping (pooled tag wrap) (before tag wrap) cells
      (pooledProgram tag wrap) input output ((row tag wrap).assignment) := by
    refine ⟨?_, position, ?_⟩
    · constructor <;> fin_cases tag <;> cases wrap <;> rfl
    · refine ⟨(entry tag wrap).mapFamily (fun _ => .jumpBranchSlt), by simp [pooledProgram], rfl, ?_, ?_⟩
      · fin_cases tag <;> cases wrap <;> decide
      · fin_cases tag <;> cases wrap <;> rfl
  have assumptions : JumpBranchSlt.Branch.InterfaceAssumptions (pooled tag wrap) (before tag wrap) cells
      (pooledProgram tag wrap) := ⟨sharedInputs tag wrap, by refine ⟨0, ?_⟩; simp [before, wordWriteState]⟩
  have core := Verification.holds_of_sublist (constraints tag wrap)
    (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
  have relation : (JumpBranchSlt.Branch.circuitModel (pooled tag wrap) (before tag wrap) cells
      (pooledProgram tag wrap)).relation input output ((row tag wrap).assignment) :=
    ⟨⟨core, pooledAccepted tag wrap, pooledDecoded tag wrap, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, JumpBranchSlt.Branch.babyBear_soundness (pooled tag wrap)
    (before tag wrap) cells (pooledProgram tag wrap) assumptions input output _ relation⟩

theorem per_circuit_pc_alias_rejected (current : State) :
    ¬ JumpBranchSlt.Branch.TraceMapping (pooled 0 false) (before 0 false) cells
      (pooledProgram 0 false)
      (⟨.BEQ, ⟨0, 0⟩, ⟨65535, 65535⟩, Branch.offset false, ⟨babyBearModulus + 4, 0⟩,
        .Regidx 1, .Regidx 2, 8188, current⟩ : JumpBranchSlt.Branch.Input)
      ⟨⟨0, 0⟩, Branch.final 0 false⟩ (row 0 false).assignment := by
  intro mapping
  have impossible := mapping.words.pcLo
  change babyBearModulus + 4 = ((row 0 false).assignment 0).val at impossible
  have small := ZMod.val_lt ((row 0 false).assignment 0)
  omega

end Tests.BranchTrace
