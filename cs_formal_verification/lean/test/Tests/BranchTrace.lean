import Slop.Sail.ResetState
import Tests.Branch
import Slop.JumpBranchSlt.Claims
import Tests.JumpHistory
import Slop.JumpBranchSlt.BranchExecution
import Slop.Verification.StaticLookup
import Mathlib.Tactic.IntervalCases

namespace Tests.BranchTrace
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768

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

private noncomputable def before (tag : Fin 6) (wrap : Bool) : State :=
  wordWriteState { Airbender.Reference.RiscV.Sail.resetMachine with regs :=
    (Airbender.Reference.RiscV.Sail.resetMachine.regs
      |>.insert .x1 (0 : BitVec 32) |>.insert .x2 (0xffffffff : BitVec 32)
      |>.insert .PC (Branch.initial wrap).toBitVec) }
    (Branch.initial wrap).toBitVec.toNat (entry tag wrap).bits

theorem airbender_before (tag : Fin 6) (wrap : Bool) : Airbender.Reference.RiscV.Sail.Configured (before tag wrap) := by
  configured_fixture [before, Airbender.Reference.RiscV.Sail.wordWriteState]


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
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · fin_cases tag <;> cases wrap <;> decide
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [JumpBranchSlt.lookup_count] using bound
      interval_cases i
      all_goals first
        | exact Verification.range16_contains (by fin_cases tag <;> cases wrap <;> decide)
        | exact Verification.static_lookup_contains _ _ _
            (by fin_cases tag <;> cases wrap <;> decide +kernel)
            (by fin_cases tag <;> cases wrap <;> decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [JumpBranchSlt.timestamp_count] using bound
      interval_cases i
      all_goals exact Proofs.range_contains (by fin_cases tag <;> cases wrap <;> decide)

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

-- Only the in-ROM (`wrap = false`) encodings are fetched; each decode is a kernel run of Sail.
private theorem instruction_decoded (tag : Fin 6) :
    decodeOnReset (entry tag false).bits = some (entry tag false).instruction := by
  fin_cases tag <;> decode_on_reset

private theorem program_image (tag : Fin 6) :
    JumpBranchSlt.programImage (before tag false) [(Branch.initial false).toBitVec] =
      some [entry tag false] := by
  have bytes : (Cell.ram (Branch.initial false).toBitVec).read (before tag false) =
      .ok (entry tag false).bits (before tag false) := written_word_read _ _ _
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, instruction_decoded, bind, Option.bind]
  fin_cases tag <;> rfl

/-- The forward-wrap fixture's PC 0xfffffffc is outside the ROM fetch domain, so the
    public decoder table rejects it even though its bytes decode. -/
theorem program_image_outside_rom_rejected (tag : Fin 6) :
    JumpBranchSlt.programImage (before tag true) [(Branch.initial true).toBitVec] = none := by
  have outside : ¬((Branch.initial true).toBitVec.toNat < ROM.limit ∧
      (Branch.initial true).toBitVec.toNat % 4 = 0) := by decide
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, outside,
    not_false_eq_true, ↓reduceIte, bind, Option.bind]

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
    negative offsets and backward wraparound (PC 0 to 0xfffffffc). Forward
    wraparound would fetch from 0xfffffffc, outside the ROM fetch domain:
    `program_image_outside_rom_rejected`. -/
theorem actual_branch_retirement (tag : Fin 6)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      initialState (retiredState (before tag false) (Branch.initial false).toBitVec) (4, 0) =
        some (trace tag false rom).initial ∧
      run (normalStep (SailRV32.Functions.execute_BTYPE 8188
        (.Regidx 2) (.Regidx 1) (opcode tag)))
        (retiredState (before tag false) (Branch.initial false).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Branch.final tag false).toBitVec) ∧
      run (SailRV32.Functions.rX_bits (.Regidx 2)) after = .ok 0xffffffff after := by
  obtain ⟨history, rows, after, _, permutation, _, execution, _⟩ :=
    JumpBranchSlt.Proofs.decoded_native_history (by decide) (by decide)
      (accepted tag false rom) (boundary tag false rom) (image tag false)
      (by decide)
      (by intro cell member; simp [cells] at member; rcases member with rfl | rfl | rfl <;> trivial)
      (program_image tag) (decoded tag false rom)
  have single : rows = [row tag false] := by
    simpa only [trace] using List.perm_singleton.mp permutation
  subst rows
  have native : SailHistory cells
      (JumpBranchSlt.Proofs.nativeEvents (trace tag false rom).memoryEpoch
        (assignment tag false)).reverse (before tag false) after := by
    simpa [Trace.rowEvents, row, Row.ports, Row.columns] using execution
  have checked := JumpBranchSlt.Proofs.branch_rebased_step (by decide) (by decide)
    (accepted tag false rom) (boundary tag false rom) (image tag false)
    (program_image tag) (decoded tag false rom)
    (by change (⟨(assignment tag false 16).val, (assignment tag false 17).val⟩ : Word).Bounded
        fin_cases tag <;> constructor <;> decide)
    (by change (assignment tag false 0).val % 4 = 0
        fin_cases tag <;> decide)
    (by simp [trace, row]) (by simp) (query tag false) (opcode tag)
    8188 1 2 rfl native (.nil _)
    ⟨Configuration.resetState.regs .misa, by simp [before, wordWriteState, Std.ExtDHashMap.get?_insert, reset_machine_get]⟩
  have written := JumpBranchSlt.Proofs.register_write (by decide)
    (trace tag false rom).memoryEpoch (query tag false) native
  change run (SailRV32.Functions.wX_bits (.Regidx 0) _) (before tag false) = .ok () after at written
  have same : before tag false = after := (EStateM.Result.ok.inj written).2
  subst after
  refine ⟨before tag false, ?_, ?_, ?_⟩
  · rw [initialState, Proofs.retired_state_pc]
    fin_cases tag <;> rfl
  · fin_cases tag <;>
      norm_num [assignment, Branch.row, Word.toBitVec, Word.value, limbBase,
        ZMod.val_ofNat, babyBearModulus] at checked ⊢
    all_goals exact checked
  · apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]

private def pooledProgram (tag : Fin 6) (wrap : Bool) : List PooledProgramEntry :=
  [(entry tag wrap).mapFamily (fun _ => .jumpBranchSlt)]

private noncomputable def pooled (tag : Fin 6) (wrap : Bool) : PooledTrace babyBearModulus where
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

private theorem pooledImage (tag : Fin 6) :
    pooledProgramImage (before tag false) [(Branch.initial false).toBitVec] = some (pooledProgram tag false) := by
  have source := Proofs.program_sources (program_image tag) (entry tag false) (by simp)
  have bytes := source.bytes
  change (Cell.ram (Branch.initial false).toBitVec).read (before tag false) = .ok (entry tag false).bits (before tag false) at bytes
  simp only [pooledProgramImage, programImageWith, List.mapM_cons, List.mapM_nil,
    programEntryWith, bytes, instruction_decoded, bind, Option.bind]
  fin_cases tag <;> rfl

private theorem pooledDecoded (tag : Fin 6) (wrap : Bool) : PooledDecoded (pooled tag wrap) (pooledProgram tag wrap) := by
  intro actual member
  simp only [pooled, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _ = _
  exact ⟨0, by fin_cases tag <;> cases wrap <;> decide⟩

private theorem pooledInputs (tag : Fin 6) :
    NativeInputs pooledDecoderFields (pooled tag false) (before tag false) cells (pooledProgram tag false) := by
  refine ⟨by decide, ?_, image tag false, ?_, ⟨[(Branch.initial false).toBitVec], pooledImage tag⟩, ?_, airbender_before tag false⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl <;> trivial
  · refine ⟨(4, 0), ?_⟩
    have read : run (SailRV32.Functions.get_arch_pc ()) (before tag false) = .ok (Branch.initial false).toBitVec (before tag false) := by
      apply read_register
      simp [before, wordWriteState]
    rw [initialState, read]
    fin_cases tag <;> rfl
  · exact ⟨(boundary tag false (ROM.table cells seed)).initial,
      (boundary tag false (ROM.table cells seed)).aligned,
      (boundary tag false (ROM.table cells seed)).memory⟩

private theorem sharedInputs (tag : Fin 6) :
    JumpBranchSlt.TraceInputs (pooled tag false) (before tag false) cells (pooledProgram tag false) := by
  refine ⟨⟨pooledInputs tag, rfl, rfl⟩, ?_, ?_⟩
  · intro actual member
    simp only [pooledProgram, List.mem_singleton] at member
    subst actual
    fin_cases tag <;> decide
  · fin_cases tag <;> constructor <;> decide

theorem per_circuit_branch_soundness (tag : Fin 6) :
    ∃ input : JumpBranchSlt.Branch.Input,
      (JumpBranchSlt.Branch.circuitModel (pooled tag false) (before tag false) cells (pooledProgram tag false)).relation
        input (⟨⟨0, 0⟩, Branch.final tag false⟩ : Output) ((row tag false).assignment) ∧
      JumpBranchSlt.Branch.InterfaceAssumptions (pooled tag false) (before tag false) cells (pooledProgram tag false) ∧
      JumpBranchSlt.Branch.spec input (⟨⟨0, 0⟩, Branch.final tag false⟩ : Output) := by
  have member : (⟨.jumpBranchSlt, (row tag false).assignment⟩ : Row babyBearModulus PooledFamily) ∈
      (pooled tag false).rows := by simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    (pooledAccepted tag false) (pooledInputs tag).clocks (pooledInputs tag).image
    (pooledInputs tag).distinct (pooledInputs tag).aligned
    (pooledImage tag) (pooledDecoded tag false) member
  let input : JumpBranchSlt.Branch.Input := ⟨opcode tag, ⟨0, 0⟩, ⟨65535, 65535⟩, Branch.offset false,
      Branch.initial false, .Regidx 1, .Regidx 2, 8188, current⟩
  let output : Output := ⟨⟨0, 0⟩, Branch.final tag false⟩
  have mapping : JumpBranchSlt.Branch.TraceMapping (pooled tag false) (before tag false) cells
      (pooledProgram tag false) input output ((row tag false).assignment) := by
    refine ⟨?_, position, ?_⟩
    · constructor <;> fin_cases tag <;> rfl
    · refine ⟨(entry tag false).mapFamily (fun _ => .jumpBranchSlt), by simp [pooledProgram], rfl, ?_, ?_⟩
      · fin_cases tag <;> decide
      · fin_cases tag <;> rfl
  have assumptions : JumpBranchSlt.Branch.InterfaceAssumptions (pooled tag false) (before tag false) cells
      (pooledProgram tag false) := ⟨sharedInputs tag, airbender_before tag false⟩
  have relation : (JumpBranchSlt.Branch.circuitModel (pooled tag false) (before tag false) cells
      (pooledProgram tag false)).relation input output ((row tag false).assignment) :=
    ⟨⟨ pooledAccepted tag false, pooledDecoded tag false, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, JumpBranchSlt.Branch.babyBear_soundness (pooled tag false)
    (before tag false) cells (pooledProgram tag false) assumptions input output _ relation⟩

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
