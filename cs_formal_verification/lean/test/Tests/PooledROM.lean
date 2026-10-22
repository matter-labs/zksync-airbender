import Tests.TraceExecution
import Slop.Trace.Claims
import Slop.SubwordMemory.Claims
import Slop.Trace.RowContext

namespace Tests.PooledROM
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- LBU x1,1(x0) reads 0x40 from its own instruction (0x00104083).
-- The native ROM read and seed stay zero; the setup uses actual public bytes.
private def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .x1 0 |>.insert .mseccfg 0
    mem := Tests.TraceExecution.before.mem.insert 0 0x83
      |>.insert 1 0x40 |>.insert 2 0x10 |>.insert 3 0 }
private def cells : List Cell := Tests.TraceExecution.cells ++ [.ram 0]
private def physical : List (MemoryToken babyBearModulus) :=
  ROMView.nativeBootImage Tests.TraceExecution.cells ++ [Cell.initialToken (.ram 0) 0x00104083]

private def assignment : Nat → ZMod babyBearModulus
  | 4 | 7 | 8 | 11 | 27 | 35 | 41 | 46 | 60 | 62 | 63 | 64 => 1
  | 2 | 13 => 4
  | 15 => 8
  | 33 | 53 | 54 | 55 => 0x40
  | 42 => 65472
  | 44 | 51 => 65536
  | 49 | 52 => 16777216
  | 50 => 131072
  | 59 | 61 => 45
  | _ => 0
private def nativeRow : Row babyBearModulus PooledFamily := ⟨.subwordMemory, assignment⟩
private def terminal : List (MemoryToken babyBearModulus) :=
  [⟨(Cell.register 0).addressCode, (4, 0), Nat.pair 0 0⟩,
   ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 0x40 0⟩] ++
  (ROMView.nativeBootImage (p := babyBearModulus) Tests.TraceExecution.cells).drop 2 ++
  [⟨(Cell.ram 0).addressCode, (5, 0), Nat.pair 0 0⟩]
private def trace : PooledTrace babyBearModulus where
  rows := [nativeRow]
  rom := ⟨ROM.table cells physical, Verification.subwordTable (ROM.words before)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := ROMView.nativeBootImage cells
  terminalMemory := terminal
private def entry : PooledProgramEntry :=
  ⟨0, 0x00104083, .LOAD (1, .Regidx 0, .Regidx 1, true, 1),
    ⟨.subwordMemory, 0, 0, 1, ⟨1, 0⟩, 2, 0⟩⟩

private theorem bytes : (Cell.ram 0).read before = .ok 0x00104083 before := by
  simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]

private theorem clearing_row (program : Nat → BitVec 32) :
    Verification.subwordRow program ⟨196609, by decide⟩ = #v[65536, 0, 0, 0, 0, 0, 0, 0, 30] := by
  norm_num [Verification.subwordRow, Verification.subwordDataRow, Verification.subwordStoreContribution]

private theorem rom_row (program : Nat → BitVec 32) :
    Verification.subwordRow program ⟨4849666, by decide⟩ =
      Verification.subwordDataRow 16777216
        (Verification.subwordLoadLimbs true ((program 0).toNat % 65536 + 131072)).1
        (Verification.subwordLoadLimbs true ((program 0).toNat % 65536 + 131072)).2 45 := by
  norm_num [Verification.subwordRow]

private theorem clear_query : trace.rom.subwordMemory.Contains #[] #v[65536, 0, 0, 0, 0, 0, 0, 0, 30] := by
  change ∃ i : Fin 13238273, (#v[65536, 0, 0, 0, 0, 0, 0, 0, 30] : Vector (ZMod babyBearModulus) 9) =
    (Verification.subwordRow (ROM.words before) i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨196609, by decide⟩, ?_⟩
  rw [clearing_row]
  apply Vector.ext
  intro index bound
  interval_cases index <;> norm_num

theorem native_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (SubwordMemory.clockConstraints trace.rom.subwordMemory) := by
  simp [SubwordMemory.clockConstraints, SubwordMemory.importedConstraints,
    SubwordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Proofs.range_contains; decide)
    | exact clear_query
    | (refine ⟨⟨4849666, by decide⟩, ?_⟩
       have word := ROM.Proofs.words_at_address (by decide : (0 : BitVec 32).toNat % 4 = 0) bytes
       change ROM.words before 0 = 0x00104083 at word
       change (#v[16777216, 64, 0, 0, 0, 0, 0, 0, 45] : Vector (ZMod babyBearModulus) 9) =
         ((Verification.subwordRow (ROM.words before) ⟨4849666, by decide⟩).map
           fun (n : Nat) => (n : ZMod babyBearModulus))
       rw [rom_row]
       rw [word]
       have concrete : Verification.subwordLoadLimbs true
           ((0x00104083 : BitVec 32).toNat % 65536 + 131072) = (64, 0) := by decide
       rw [concrete]
       simp only [Verification.subwordDataRow]
       apply Vector.ext
       intro index bound
       interval_cases index <;> norm_num)

theorem native_accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact native_constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem decoded : PooledDecoded trace [entry] := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change ∃ i : Fin 1, _
  exact ⟨0, by decide⟩

theorem preserved_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (PooledROMView.row before nativeRow).assignment)
    ((PooledROMView.row before nativeRow).constraints trace.rom) :=
  PooledROMView.row_holds before nativeRow trace.rom native_constraints

theorem distinct_rom_views :
    assignment 25 = 0 ∧ assignment 26 = 0 ∧ assignment 33 = 0x40 ∧
      (PooledROMView.row before nativeRow).assignment 25 = 0x4083 ∧
      (PooledROMView.row before nativeRow).assignment 26 = 0x10 := by
  have word := ROMView.public_word_read bytes
  simp [PooledROMView.row, PooledROMView.subwordReadData, nativeRow, assignment,
    Cell.addressCode, Word.ofBitVec, limbBase] at word ⊢
  rw [word]
  decide

private theorem zero_registers : ∀ index, (Cell.register index).read before = .ok 0 before := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before = .ok 0 before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
  intro index
  simpa using numeric index.toNat index.isLt

private theorem image : initialImage before cells = some physical := by
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.cons_append, List.nil_append,
    List.mapM_cons, List.mapM_nil, zero_registers, bytes, bind, Option.bind]
  rfl

private theorem profile : InitialProfile before cells := by
  refine ⟨?_, zero_registers, ?_⟩
  · apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · intro address member bound
    have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
    subst address
    change 4194304 ≤ 0 at bound
    omega

private theorem configuration : FlatMemoryConfiguration before := by
  constructor
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.privilege
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.status
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.isa
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.supervisorEnvironment
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.machineEnvironment
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.pmpOff
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.pmpAddresses
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.pma
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.hart
  · simpa [before, Std.ExtDHashMap.get?_insert] using Tests.TraceExecution.configuration.htifDisabled

private theorem inputs  : PooledBootInputs trace before cells [entry] := by
  refine {
    registers := fun index => List.mem_append_left _ (Tests.TraceExecution.inputs.registers index)
    distinct := by decide
    aligned := by
      intro cell member
      rcases List.mem_append.mp member with original | added
      · exact Tests.TraceExecution.inputs.aligned cell original
      · have same := List.mem_singleton.mp added
        subst cell
        trivial
    ordinary := by
      intro address member
      have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
      subst address
      unfold OrdinaryWordAddress
      decide
    configuration := configuration
    landingPadDisabled := ⟨0, by simp [before], rfl⟩
    programImage := ⟨[0], by
      simp only [programImageRunWith, List.mapM_cons, List.mapM_nil,
        programEntryRunWith, bytes, bind, Option.bind]
      rfl⟩
    code := by
      intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      constructor <;> decide
    loads := by simp [NoDiscardedLoads, entry]
    profile := profile
    seed := rfl
    initialBoundary := rfl
    physicalImage := ⟨physical, image, rfl⟩
    subwordSetup := rfl
    terminalPC := ⟨by decide, by decide⟩ }

/-- The primary native claim is inhabited by a nonzero public ROM-byte load.
    Initialization, actual decoding and setup binding are all proved here. -/
theorem complete_rom_load  :
    ∃ after, Relation.ReflTransGen (PooledStep [entry]) before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 4 after ∧
      (Cell.register 1).read after = .ok 0x40 after := by
  obtain ⟨after, execution, pc, terminal⟩ := pooled_native_soundness inputs native_accepted decoded
  refine ⟨after, execution, pc, ?_⟩
  have read := terminal ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 0x40 0⟩
    (by simp [trace, Tests.PooledROM.terminal])
  obtain ⟨cell, _, equal, actual⟩ := read
  have same : cell = .register 1 := Proofs.cell_address_injective equal
  subst cell
  simpa [ROMView.token, ROMView.shadow, Cell.addressCode, MemoryToken.word,
    Word.toBitVec, Word.value, limbBase] using actual

/-- The subword per-circuit claim also covers the public ROM-byte fixture.
    The proved physical view binds reads to public bytes while native shadow
    tokens stay zero; no input bound or desired-read interface is supplied. -/
theorem per_circuit_rom_load  :
    ∃ input : SubwordMemory.Input,
      (SubwordMemory.circuitModel (PooledROMView.data before trace) before cells [entry]).relation
        input ⟨⟨0, 0⟩, ⟨64, 0⟩, ⟨4, 0⟩⟩ (PooledROMView.row before nativeRow).assignment ∧
      SubwordMemory.InterfaceAssumptions (PooledROMView.data before trace) before cells [entry] ∧
      SubwordMemory.spec input ⟨⟨0, 0⟩, ⟨64, 0⟩, ⟨4, 0⟩⟩ := by
  let view := PooledROMView.data before trace
  let w := (PooledROMView.row before nativeRow).assignment
  have boundary := PooledROMView.execution_boundary (by decide) inputs
  have accepted := PooledROMView.accepted (by decide) (by decide) before native_accepted
    (ROMView.native_clocks (by decide) inputs.seed inputs.initialBoundary) inputs.seed
  have query := PooledROMView.decoded before decoded
  have member : (⟨.subwordMemory, w⟩ : Row babyBearModulus PooledFamily) ∈ view.rows := by
    simp only [view, PooledROMView.data, trace, List.map_cons, List.map_nil, List.mem_singleton]
    rfl
  obtain ⟨addresses, programImage⟩ := boundary.programImage
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    accepted boundary.clocks boundary.image boundary.distinct boundary.aligned programImage query member
  let input : SubwordMemory.Input :=
    ⟨false, true, false, ⟨0, 0⟩, ⟨1, 0⟩, ⟨(w 25).val, (w 26).val⟩, ⟨0, 0⟩,
      ⟨0, 0⟩, .Regidx 0, .Regidx 0, .Regidx 1, 1, current⟩
  let output : SubwordMemory.Output := ⟨⟨0, 0⟩, ⟨64, 0⟩, ⟨4, 0⟩⟩
  have mapping : SubwordMemory.TraceMapping view before cells [entry] input output w := by
    refine ⟨?_, position, ?_⟩
    · constructor
      all_goals first | rfl | (intro impossible; contradiction)
    · exact ⟨entry, by simp, rfl, by decide, rfl⟩
  have assumptions : SubwordMemory.InterfaceAssumptions view before cells [entry] :=
    ⟨⟨boundary.toNativeInputs, boundary.wordSetup, boundary.subwordSetup⟩, inputs.ordinary, configuration⟩
  have relation : (SubwordMemory.circuitModel view before cells [entry]).relation input output w :=
    ⟨⟨ accepted, query, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, SubwordMemory.babyBear_soundness view before cells [entry] assumptions
    input output w relation⟩

/-- Canonical source mapping excludes field aliases without a local range premise. -/
theorem per_circuit_source_alias_rejected (current : State) :
    ¬ SubwordMemory.TraceMapping (PooledROMView.data before trace) before cells [entry]
      (⟨false, true, false, ⟨babyBearModulus, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
        ⟨0, 0⟩, .Regidx 0, .Regidx 0, .Regidx 1, 1, current⟩ : SubwordMemory.Input)
      ⟨⟨0, 0⟩, ⟨64, 0⟩, ⟨4, 0⟩⟩ (PooledROMView.row before nativeRow).assignment := by
  intro mapping
  have impossible := mapping.words.sourceLo
  change babyBearModulus = ((PooledROMView.row before nativeRow).assignment 19).val at impossible
  have small := ZMod.val_lt ((PooledROMView.row before nativeRow).assignment 19)
  omega

end Tests.PooledROM
