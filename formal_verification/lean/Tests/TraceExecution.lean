import Tests.TraceMemory

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
  simp only [programImage, List.mapM_cons, List.mapM_nil, programEntry,
    first, second, decodeFirst, decodeSecond, bind, Option.bind]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem configuration : FlatMemoryConfiguration before := by
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
theorem complete_dependent_trace [MemoryPlatform SailRV32.exception] :
    ∃ after, SailTrace Tests.TraceMemory.sequentialProgram before after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after = .ok 8 after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Proofs.memoryWord sink.value) after :=
  Trace.sail_soundness inputs noDiscardedLoads accepted decoded

end Tests.TraceExecution
