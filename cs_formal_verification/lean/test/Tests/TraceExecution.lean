import Slop.AddSub.RowClaims
import Tests.TraceMemory
import Slop.Final.Circuits.AddSub.Theorems

namespace Tests.TraceExecution
open Airbender Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- The same two dependent, reversed ADD rows, with a complete public GPR image
-- and actual Machine/PMA/PMP configuration for the shared trace boundary.
private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

def before : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes]
      |>.insert .mhartid 7 |>.insert .htif_tohost_base none |>.insert .PC (0 : BitVec 32)
      |>.insert .x1 5
      |>.insert .x2 0
      |>.insert .x3 0
      |>.insert .x4 0
      |>.insert .x5 0
      |>.insert .x6 0
      |>.insert .x7 0
      |>.insert .x8 0
      |>.insert .x9 0
      |>.insert .x10 0
      |>.insert .x11 0
      |>.insert .x12 0
      |>.insert .x13 0
      |>.insert .x14 0
      |>.insert .x15 0
      |>.insert .x16 0
      |>.insert .x17 0
      |>.insert .x18 0
      |>.insert .x19 0
      |>.insert .x20 0
      |>.insert .x21 0
      |>.insert .x22 0
      |>.insert .x23 0
      |>.insert .x24 0
      |>.insert .x25 0
      |>.insert .x26 0
      |>.insert .x27 0
      |>.insert .x28 0
      |>.insert .x29 0
      |>.insert .x30 0
      |>.insert .x31 0
    mem := Tests.TraceMemory.sequentialBefore.mem }

def cells : List Cell :=
  [.register 0, .register 1, .register 2, .register 3, .register 4, .register 5, .register 6, .register 7, .register 8, .register 9, .register 10, .register 11, .register 12, .register 13, .register 14, .register 15, .register 16, .register 17, .register 18, .register 19, .register 20, .register 21, .register 22, .register 23, .register 24, .register 25, .register 26, .register 27, .register 28, .register 29, .register 30, .register 31]

private def initial : List (MemoryToken babyBearModulus) :=
  (List.range 32).map fun index =>
    ⟨Nat.pair 0 (Nat.pair index 0), (0, 0), Nat.pair (if index = 1 then 5 else 0) 0⟩

private def trace : Data babyBearModulus :=
  { Tests.TraceMemory.twoRows Tests.TraceMemory.publicROM with
    initialMemory := initial
    terminalMemory := (Tests.TraceMemory.twoRows Tests.TraceMemory.publicROM).terminalMemory ++ initial.drop 3
    rom := ROM.table cells initial }

private theorem image : initialImage before cells = some trace.initialMemory := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before =
        .ok (if index = 1 then 5 else 0) before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, Std.ExtDHashMap.get?_insert])
  have reads : ∀ index : BitVec 5, (Cell.register index).read before =
      .ok (if index.toNat = 1 then 5 else 0) before := by
    intro index
    simpa using numeric index.toNat index.isLt
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, reads, bind, Option.bind]
  rfl

private theorem accepted : Accepted trace := by
  have old := Tests.TraceMemory.two_accepted Tests.TraceMemory.publicROM
  refine ⟨?_, old.active, old.states, ?_⟩
  · intro actual member
    rcases List.mem_cons.mp member with rfl | present
    · exact Tests.TraceMemory.second_satisfies
    · have same := List.mem_singleton.mp present
      subst actual
      exact Tests.TraceMemory.local_satisfies
  · decide

private theorem decoded : Decoded trace Tests.TraceMemory.sequentialProgram :=
  Tests.TraceMemory.sequential_decoded

private theorem program_image : programImage before [0, 4] =
    some Tests.TraceMemory.sequentialProgram := by
  have old := Proofs.program_sources Tests.TraceMemory.sequential_program_image
  have first := read_word_frame (before := Tests.TraceMemory.sequentialBefore) (after := before) rfl (old
    Tests.TraceMemory.sequentialProgram[0] (by simp [Tests.TraceMemory.sequentialProgram,
      Tests.TraceMemory.publicProgram])).bytes
  have second := read_word_frame (before := Tests.TraceMemory.sequentialBefore) (after := before) rfl (old
    Tests.TraceMemory.sequentialProgram[1] (by simp [Tests.TraceMemory.sequentialProgram,
      Tests.TraceMemory.publicProgram])).bytes
  change (Cell.ram 0).read before = .ok 0x00008133 before at first
  change (Cell.ram 4).read before = .ok 0x002100b3 before at second
  have decodeFirst : SailRV32.Functions.encdec_backwards 0x00008133 =
      (FreeM.pure (.RTYPE (.Regidx 0, .Regidx 1, .Regidx 2, .ADD)) : SailRV32.SailM _) := rfl
  have decodeSecond : SailRV32.Functions.encdec_backwards 0x002100b3 =
      (FreeM.pure (.RTYPE (.Regidx 2, .Regidx 2, .Regidx 1, .ADD)) : SailRV32.SailM _) := rfl
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith,
    first, second, decodeFirst, decodeSecond, bind, Option.bind]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem configuration : Configured before := by
  constructor
  · simp [before, Std.ExtDHashMap.get?_insert]
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [before, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨7, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]

theorem inputs : ExecutionBoundary trace before cells Tests.TraceMemory.sequentialProgram := by
  refine {
    image := image
    initialPC := ⟨(4, 0), ?_⟩
    rom := rfl
    registers := ?_
    distinct := ?_
    aligned := ?_
    ordinary := ?_
    configuration := configuration
    programImage := ⟨[0, 4], program_image⟩
    code := ?_
    clocks := ?_ }
  · intro index
    have encoded : index = BitVec.ofNat 5 index.toNat := by simp
    rw [encoded]
    have bound := index.isLt
    interval_cases index.toNat <;> decide
  · decide
  · intro cell present
    have registers : ∀ cell ∈ cells, ∃ index, cell = .register index := by
      decide
    obtain ⟨index, rfl⟩ := registers cell present
    trivial
  · intro address present
    simp [cells] at present
  · intro entry present
    simp only [Tests.TraceMemory.sequentialProgram, Tests.TraceMemory.publicProgram,
      List.mem_append, List.mem_singleton] at present
    rcases present with rfl | rfl <;> decide
  · have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
      apply read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    rw [initialState, pc]
    rfl
  · refine ⟨?_, ?_, Proofs.image_clocks image⟩
    · change 4 < timestampBase ∧ 0 < timestampBase
      constructor <;> decide
    · change 4 % 4 = 0
      decide

private theorem noDiscardedLoads : NoDiscardedLoads Tests.TraceMemory.sequentialProgram := by
  intro entry present imm rs1
  simp only [Tests.TraceMemory.sequentialProgram, Tests.TraceMemory.publicProgram,
    List.mem_append, List.mem_singleton] at present
  rcases present with rfl | rfl <;> intro impossible <;> cases impossible

/-- The whole-trace theorem executes both actual public-decoded instructions
    and fixes every terminal GPR value, including untouched initialized cells. -/
theorem complete_dependent_trace  :
    ∃ after, SailTrace Tests.TraceMemory.sequentialProgram before after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after = .ok 8 after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord sink.value) after :=
  Trace.sail_soundness inputs noDiscardedLoads accepted decoded

private def pooledProgram : List PooledProgramEntry :=
  Tests.TraceMemory.sequentialProgram.map (ProgramEntry.mapFamily pooledArithmeticFamily)

private def pooled : PooledTrace babyBearModulus where
  rows := [⟨.addSub, Tests.TraceMemory.secondRow.assignment⟩,
    ⟨.addSub, Tests.TraceMemory.row.assignment⟩]
  rom := ⟨trace.rom, Verification.subwordTable (ROM.words before)⟩
  initial := trace.initial
  terminal := trace.terminal
  initialMemory := trace.initialMemory
  terminalMemory := trace.terminalMemory

private theorem pooledAccepted : Accepted pooled := by
  constructor
  · intro row member
    simp [pooled] at member
    rcases member with rfl | rfl
    · exact Tests.TraceMemory.second_satisfies
    · exact Tests.TraceMemory.local_satisfies
  · intro row member
    simp [pooled] at member
    rcases member with rfl | rfl <;> rfl
  · exact accepted.states
  · exact accepted.memory

private theorem pooledDecoded : PooledDecoded pooled pooledProgram := by
  intro row member
  simp [pooled] at member
  rcases member with rfl | rfl
  · change ∃ i : Fin 2, _ = _
    exact ⟨1, by decide⟩
  · change ∃ i : Fin 2, _ = _
    exact ⟨0, by decide⟩

private theorem pooledImage : pooledProgramImage before [0, 4] = some pooledProgram := by
  have sources := Proofs.program_sources program_image
  have first := (sources Tests.TraceMemory.sequentialProgram[0]
    (by simp [Tests.TraceMemory.sequentialProgram, Tests.TraceMemory.publicProgram])).bytes
  have second := (sources Tests.TraceMemory.sequentialProgram[1]
    (by simp [Tests.TraceMemory.sequentialProgram, Tests.TraceMemory.publicProgram])).bytes
  change (Cell.ram 0).read before = .ok 0x00008133 before at first
  change (Cell.ram 4).read before = .ok 0x002100b3 before at second
  simp only [pooledProgramImage, programImageWith, List.mapM_cons, List.mapM_nil,
    programEntryWith, first, second, bind, Option.bind]
  rfl

private theorem pooledInputs : NativeInputs pooledDecoderFields pooled before cells pooledProgram :=
  ⟨inputs.distinct, inputs.aligned, inputs.image, inputs.initialPC,
    ⟨[0, 4], pooledImage⟩, ⟨inputs.clocks.initial, inputs.clocks.aligned, inputs.clocks.memory⟩⟩

/-- The second ADD reads the first ADD's write through the per-circuit model.
    All public premises are inhabited; no read or input-range hypothesis is used. -/
theorem addsub_per_circuit_soundness :
    ∃ input : Input,
      (AddSub.circuitModel pooled before cells pooledProgram).relation input
        ⟨⟨10, 0⟩, ⟨8, 0⟩⟩ Tests.TraceMemory.secondRow.assignment ∧
      AddSub.InterfaceAssumptions pooled before cells pooledProgram ∧
      spec input ⟨⟨10, 0⟩, ⟨8, 0⟩⟩ := by
  have member : (⟨.addSub, Tests.TraceMemory.secondRow.assignment⟩ : Row babyBearModulus PooledFamily) ∈
      pooled.rows := by simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    pooledAccepted pooledInputs.clocks pooledInputs.image pooledInputs.distinct pooledInputs.aligned
    pooledImage pooledDecoded member
  let input := Proofs.arithmeticInput .add 2 2 1 0 0 Tests.TraceMemory.secondRow.assignment current
  have mapping : AddSub.TraceMapping pooled before cells pooledProgram input
      ⟨⟨10, 0⟩, ⟨8, 0⟩⟩ Tests.TraceMemory.secondRow.assignment := by
    refine ⟨?_, position, ?_⟩
    · constructor <;> rfl
    refine ⟨pooledProgram[1], ?_, rfl, rfl, rfl⟩
    simp [pooledProgram, Tests.TraceMemory.sequentialProgram, Tests.TraceMemory.publicProgram]
  have assumptions : AddSub.InterfaceAssumptions pooled before cells pooledProgram :=
    ⟨⟨pooledInputs, rfl, rfl⟩, inputs.registers⟩
  have core := Verification.holds_of_sublist Tests.TraceMemory.second_satisfies
    (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
  have relation : (AddSub.circuitModel pooled before cells pooledProgram).relation input
      ⟨⟨10, 0⟩, ⟨8, 0⟩⟩ Tests.TraceMemory.secondRow.assignment :=
    ⟨⟨pooledAccepted, pooledDecoded, member⟩, mapping⟩
  exact ⟨input, relation, assumptions,
    AddSub.babyBear_soundness pooled before cells pooledProgram assumptions input _ _ relation⟩

/-- Canonical mapping excludes an unbounded field alias of the input five. -/
theorem addsub_field_alias_rejected (current : State) :
    ¬ AddSub.TraceMapping pooled before cells pooledProgram
      { Proofs.arithmeticInput .add 2 2 1 0 0 Tests.TraceMemory.secondRow.assignment current with
        row := ⟨.add, ⟨babyBearModulus + 5, 0⟩, ⟨5, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩⟩ }
      ⟨⟨10, 0⟩, ⟨8, 0⟩⟩ Tests.TraceMemory.secondRow.assignment := by
  intro mapping
  have impossible := mapping.words.leftLo
  change babyBearModulus + 5 = (Tests.TraceMemory.secondRow.assignment 25).val at impossible
  have small := ZMod.val_lt (Tests.TraceMemory.secondRow.assignment 25)
  omega

end Tests.TraceExecution
