import Tests.AirbenderInitialization
import Tests.DelegationCaller
import Airbender.Proofs.Sail.VirtualMemory
import Airbender.Proofs.Sail.Memory
import Airbender.Proofs.Sail.ControlFlow
import Airbender.Proofs.Trace.ImageInstall
import Airbender.Proofs.Trace.ProgramConstruction
import Airbender.Review.Circuits.UnifiedReduced.Decoder
import Airbender.Review.Trace.Execution

namespace Tests.DynamicCopyLoopProgram
open Airbender Airbender.Trace Airbender.Arithmetic
open Airbender.Reference Airbender.Reference.Sail Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- Public instruction bytes and the expected original Sail instruction. This
record carries no decoder, native-acceptance, or successful-execution assumption. -/
structure CodeEntry where
  pc : BitVec 32
  bits : BitVec 32
  instruction : SailRV32.instruction

/-- The twelve distinct code locations. The COPY CSR at 132 is retained in the
public image even though it has no ordinary unified decoder projection. -/
def codeEntry (index : Fin 12) : CodeEntry :=
  match index.val with
  | 0 => ⟨0, 0x00200293, .ITYPE (2, .Regidx 0, .Regidx 5, .ADDI)⟩
  | 1 => ⟨4, 0x02000537, .UTYPE (0x02000, .Regidx 10, .LUI)⟩
  | 2 => ⟨8, 0x02050593, .ITYPE (32, .Regidx 10, .Regidx 11, .ADDI)⟩
  | 3 => ⟨12, 0x00700113, .ITYPE (7, .Regidx 0, .Regidx 2, .ADDI)⟩
  | 4 => ⟨16, 0x0025a023, .STORE (0, .Regidx 2, .Regidx 11, 4)⟩
  | 5 => ⟨20, 0x06c0006f, .JAL (108, .Regidx 0)⟩
  | 6 => ⟨128, 0x00000617, .UTYPE (0, .Regidx 12, .AUIPC)⟩
  | 7 => ⟨132, 0x7ca01073, .CSRReg (0x7ca, .Regidx 0, .Regidx 0, .CSRRW)⟩
  | 8 => ⟨136, 0xfff28293, .ITYPE (0xfff, .Regidx 5, .Regidx 5, .ADDI)⟩
  | 9 => ⟨140, 0xfe029ae3, .BTYPE (0x1ff4, .Regidx 0, .Regidx 5, .BNE)⟩
  | 10 => ⟨144, 0x008000ef, .JAL (8, .Regidx 1)⟩
  | _ => ⟨152, 0x00808067, .JALR (8, .Regidx 1, .Regidx 0)⟩

def codeIndices : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def code : List CodeEntry := codeIndices.map codeEntry

def install : List CodeEntry → State → State
  | [], state => state
  | entry :: rest, state => install rest (wordWriteState state entry.pc.toNat entry.bits)

/-- Actual zero-GPR, zero-RAM boot state with only the public code installed. -/
noncomputable def before : State := install code AirbenderInitialization.before

def destinationAddress : BitVec 32 := 33554432
def sourceAddress : BitVec 32 := 33554464

/-- Each encoding is checked by the unchanged stateful upstream decoder. -/
theorem original_decode (index : Fin 12) (state : State) :
    run (SailRV32.Functions.encdec_backwards (codeEntry index).bits) state =
      .ok (codeEntry index).instruction state := by
  fin_cases index
  all_goals first
    | rfl
    | (change run (SailRV32.Functions.encdec_backwards 0x7ca01073) state =
         .ok (.CSRReg (0x7ca, .Regidx 0, .Regidx 0, .CSRRW)) state
       exact Tests.DelegationCaller.original_decoder .bigint state)

private theorem fetch_0 : (Cell.ram 0).read before = .ok 0x00200293 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  apply written_word_disjoint 132 0x7ca01073 (by decide)
  apply written_word_disjoint 128 0x00000617 (by decide)
  apply written_word_disjoint 20 0x06c0006f (by decide)
  apply written_word_disjoint 16 0x0025a023 (by decide)
  apply written_word_disjoint 12 0x00700113 (by decide)
  apply written_word_disjoint 8 0x02050593 (by decide)
  apply written_word_disjoint 4 0x02000537 (by decide)
  exact written_word_read _ _ _

private theorem fetch_4 : (Cell.ram 4).read before = .ok 0x02000537 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  apply written_word_disjoint 132 0x7ca01073 (by decide)
  apply written_word_disjoint 128 0x00000617 (by decide)
  apply written_word_disjoint 20 0x06c0006f (by decide)
  apply written_word_disjoint 16 0x0025a023 (by decide)
  apply written_word_disjoint 12 0x00700113 (by decide)
  apply written_word_disjoint 8 0x02050593 (by decide)
  exact written_word_read _ _ _

private theorem fetch_8 : (Cell.ram 8).read before = .ok 0x02050593 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  apply written_word_disjoint 132 0x7ca01073 (by decide)
  apply written_word_disjoint 128 0x00000617 (by decide)
  apply written_word_disjoint 20 0x06c0006f (by decide)
  apply written_word_disjoint 16 0x0025a023 (by decide)
  apply written_word_disjoint 12 0x00700113 (by decide)
  exact written_word_read _ _ _

private theorem fetch_12 : (Cell.ram 12).read before = .ok 0x00700113 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  apply written_word_disjoint 132 0x7ca01073 (by decide)
  apply written_word_disjoint 128 0x00000617 (by decide)
  apply written_word_disjoint 20 0x06c0006f (by decide)
  apply written_word_disjoint 16 0x0025a023 (by decide)
  exact written_word_read _ _ _

private theorem fetch_16 : (Cell.ram 16).read before = .ok 0x0025a023 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  apply written_word_disjoint 132 0x7ca01073 (by decide)
  apply written_word_disjoint 128 0x00000617 (by decide)
  apply written_word_disjoint 20 0x06c0006f (by decide)
  exact written_word_read _ _ _

private theorem fetch_20 : (Cell.ram 20).read before = .ok 0x06c0006f before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  apply written_word_disjoint 132 0x7ca01073 (by decide)
  apply written_word_disjoint 128 0x00000617 (by decide)
  exact written_word_read _ _ _

private theorem fetch_128 : (Cell.ram 128).read before = .ok 0x00000617 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  apply written_word_disjoint 132 0x7ca01073 (by decide)
  exact written_word_read _ _ _

private theorem fetch_132 : (Cell.ram 132).read before = .ok 0x7ca01073 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  apply written_word_disjoint 136 0xfff28293 (by decide)
  exact written_word_read _ _ _

private theorem fetch_136 : (Cell.ram 136).read before = .ok 0xfff28293 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  apply written_word_disjoint 140 0xfe029ae3 (by decide)
  exact written_word_read _ _ _

private theorem fetch_140 : (Cell.ram 140).read before = .ok 0xfe029ae3 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  apply written_word_disjoint 144 0x008000ef (by decide)
  exact written_word_read _ _ _

private theorem fetch_144 : (Cell.ram 144).read before = .ok 0x008000ef before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  apply written_word_disjoint 152 0x00808067 (by decide)
  exact written_word_read _ _ _

private theorem fetch_152 : (Cell.ram 152).read before = .ok 0x00808067 before := by
  dsimp only [before, install, code, codeIndices, List.map, codeEntry]
  exact written_word_read _ _ _

/-- Every public instruction word is read from the actual installed memory.
Separate concrete reads avoid speculative unification through the whole boot state. -/
theorem fetch (index : Fin 12) :
    (Cell.ram (codeEntry index).pc).read before = .ok (codeEntry index).bits before := by
  fin_cases index
  · exact fetch_0
  · exact fetch_4
  · exact fetch_8
  · exact fetch_12
  · exact fetch_16
  · exact fetch_20
  · exact fetch_128
  · exact fetch_132
  · exact fetch_136
  · exact fetch_140
  · exact fetch_144
  · exact fetch_152

private theorem install_registers (entries : List CodeEntry) (state : State) :
    (install entries state).regs = state.regs := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact ih (wordWriteState state entry.pc.toNat entry.bits)

private theorem install_configuration (entries : List CodeEntry) {state : State}
    (configured : FlatMemoryConfiguration state) : FlatMemoryConfiguration (install entries state) := by
  induction entries generalizing state with
  | nil => exact configured
  | cons entry rest ih =>
    exact ih (configuration_word_write configured entry.pc.toNat entry.bits)

theorem configuration : FlatMemoryConfiguration before :=
  install_configuration code AirbenderInitialization.configuration

theorem registers_zero (index : BitVec 5) :
    (Cell.register index).read before = .ok 0 before :=
  rX_register_frame (install_registers code AirbenderInitialization.before) index
    (AirbenderInitialization.registers_zero index)

theorem initial_pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
  apply read_register
  rw [show before.regs = AirbenderInitialization.before.regs from install_registers _ _]
  exact read_register_iff.mp AirbenderInitialization.standalone_profile.profile.pc

/-- These are actual CSR reads, including the extra Machine/MLPE condition
needed by the original JALR clause. -/
theorem initial_misa : run (SailRV32.readReg .misa) before = .ok 0x40000100 before := by
  apply read_register
  rw [show before.regs = AirbenderInitialization.before.regs from install_registers _ _]
  simp [AirbenderInitialization.before, Std.ExtDHashMap.get?_insert]

theorem initial_privilege :
    run (SailRV32.readReg .cur_privilege) before = .ok .Machine before := by
  apply read_register
  rw [show before.regs = AirbenderInitialization.before.regs from install_registers _ _]
  simp [AirbenderInitialization.before, Std.ExtDHashMap.get?_insert]

theorem initial_security : run (SailRV32.readReg .mseccfg) before = .ok 0 before := by
  apply read_register
  rw [show before.regs = AirbenderInitialization.before.regs from install_registers _ _]
  simp [AirbenderInitialization.before, Std.ExtDHashMap.get?_insert]

private theorem code_aligned (entry : CodeEntry) (member : entry ∈ code) : entry.pc.toNat % 4 = 0 := by
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  fin_cases index <;> decide

private theorem install_image (entries : List CodeEntry) {state : State}
    {domain : List Cell} {image : List (MemoryToken babyBearModulus)}
    (source : initialImage state domain = some image)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (codeAligned : ∀ entry ∈ entries, entry.pc.toNat % 4 = 0) :
    ∃ physical : List (MemoryToken babyBearModulus),
      initialImage (install entries state) domain = some physical := by
  induction entries generalizing state image with
  | nil => exact ⟨image, source⟩
  | cons entry rest ih =>
    obtain ⟨next, written⟩ := Trace.Proofs.image_word_write_exists source aligned
      entry.pc.toNat (codeAligned entry (by simp)) entry.bits
    exact ih written (fun item member => codeAligned item (by simp [member]))

theorem physical_image {domain : List Cell} {image : List (MemoryToken babyBearModulus)}
    (source : initialImage AirbenderInitialization.before domain = some image)
    (aligned : ∀ cell ∈ domain, cell.Aligned) :
    ∃ physical : List (MemoryToken babyBearModulus), initialImage before domain = some physical :=
  install_image code source aligned code_aligned

private theorem install_preserves_read (entries : List CodeEntry) {state : State}
    {address : Nat} {value : BitVec 32}
    (apart : ∀ entry ∈ entries, address + 4 ≤ entry.pc.toNat ∨ entry.pc.toNat + 4 ≤ address)
    (read : (readBytes (ue := SailRV32.exception) 4 address).run state = .ok value state) :
    (readBytes (ue := SailRV32.exception) 4 address).run (install entries state) =
      .ok value (install entries state) := by
  induction entries generalizing state with
  | nil => exact read
  | cons entry rest ih =>
    exact ih (fun item member => apart item (by simp [member]))
      (written_word_disjoint entry.pc.toNat entry.bits (apart entry (by simp)) read)

/-- Every bounded boot-memory word disjoint from the installed code stays zero. -/
theorem initial_ram (address : BitVec 32) (bound : address.toNat + 4 ≤ 2 ^ 30)
    (apart : ∀ index : Fin 12, address.toNat + 4 ≤ (codeEntry index).pc.toNat ∨
      (codeEntry index).pc.toNat + 4 ≤ address.toNat) :
    (Cell.ram address).read before = .ok 0 before := by
  apply install_preserves_read code
  · intro entry member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    exact apart index
  · exact zeroMemory_word (before := AirbenderInitialization.before) rfl bound

private theorem code_end (index : Fin 12) : (codeEntry index).pc.toNat + 4 ≤ 156 := by
  fin_cases index <;> decide

theorem destination_block_zero (index : Fin 8) :
    (Cell.ram (destinationAddress + 4 * BitVec.ofNat 32 index.val)).read before = .ok 0 before := by
  apply initial_ram
  · fin_cases index <;> decide
  · intro codeIndex
    right
    have last := code_end codeIndex
    have large : 156 ≤ (destinationAddress + 4 * BitVec.ofNat 32 index.val).toNat := by
      fin_cases index <;> decide
    omega

theorem source_block_zero (index : Fin 8) :
    (Cell.ram (sourceAddress + 4 * BitVec.ofNat 32 index.val)).read before = .ok 0 before := by
  apply initial_ram
  · fin_cases index <;> decide
  · intro codeIndex
    right
    have last := code_end codeIndex
    have large : 156 ≤ (sourceAddress + 4 * BitVec.ofNat 32 index.val).toNat := by
      fin_cases index <;> decide
    omega

/-- Skip only the custom CSR entry; ordinary metadata is computed by the
existing unified decoder, never copied into a handwritten replacement table. -/
def ordinaryIndex (index : Fin 11) : Fin 12 :=
  ⟨if index.val < 7 then index.val else index.val + 1, by split <;> omega⟩

private theorem ordinary_fields_present (index : Fin 11) :
    (UnifiedReduced.decoderFields (codeEntry (ordinaryIndex index)).instruction).isSome := by
  fin_cases index <;> decide

def ordinaryEntry (index : Fin 11) : ProgramEntry UnifiedFamily :=
  let entry := codeEntry (ordinaryIndex index)
  ⟨entry.pc, entry.bits, entry.instruction,
    (UnifiedReduced.decoderFields entry.instruction).get (ordinary_fields_present index)⟩

def ordinaryIndices : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def ordinaryProgram : List (ProgramEntry UnifiedFamily) := ordinaryIndices.map ordinaryEntry

theorem ordinary_pcs : ordinaryProgram.map ProgramEntry.pc =
    [0, 4, 8, 12, 16, 20, 128, 136, 140, 144, 152] := rfl

theorem ordinary_fields (index : Fin 11) :
    UnifiedReduced.decoderFields (ordinaryEntry index).instruction = some (ordinaryEntry index).data :=
  (Option.some_get (ordinary_fields_present index)).symm

theorem ordinary_source (index : Fin 11) :
    (ordinaryEntry index).SourceWith before UnifiedReduced.decoderFields :=
  ⟨fetch (ordinaryIndex index), original_decode (ordinaryIndex index) before, ordinary_fields index⟩

theorem ordinary_entry_run (index : Fin 11) :
    programEntryRunWith UnifiedReduced.decoderFields before (ordinaryEntry index).pc =
      some (ordinaryEntry index) :=
  Trace.Proofs.program_entry_run_of_reads _ _ _ _ _ _
    (ordinary_source index).bytes (ordinary_source index).decoded (ordinary_source index).fields

theorem ordinary_program_image :
    programImageRunWith UnifiedReduced.decoderFields before
      [0, 4, 8, 12, 16, 20, 128, 136, 140, 144, 152] = some ordinaryProgram := by
  change programImageRunWith UnifiedReduced.decoderFields before
    [(ordinaryEntry 0).pc, (ordinaryEntry 1).pc, (ordinaryEntry 2).pc,
      (ordinaryEntry 3).pc, (ordinaryEntry 4).pc, (ordinaryEntry 5).pc,
      (ordinaryEntry 6).pc, (ordinaryEntry 7).pc, (ordinaryEntry 8).pc,
      (ordinaryEntry 9).pc, (ordinaryEntry 10).pc] = _
  simp only [programImageRunWith, List.mapM_cons, List.mapM_nil,
    ordinary_entry_run 0, ordinary_entry_run 1, ordinary_entry_run 2,
    ordinary_entry_run 3, ordinary_entry_run 4, ordinary_entry_run 5,
    ordinary_entry_run 6, ordinary_entry_run 7, ordinary_entry_run 8,
    ordinary_entry_run 9, ordinary_entry_run 10, bind, Option.bind, pure]
  rfl

/-- Fetch preservation for later ordinary states is a memory-frame fact. The
mixed execution integrator must establish its frame from the actual history. -/
theorem ordinary_source_frame (index : Fin 11) {state : State} (memory : state.mem = before.mem) :
    (ordinaryEntry index).SourceWith state UnifiedReduced.decoderFields :=
  ⟨read_word_frame memory (ordinary_source index).bytes,
    original_decode (ordinaryIndex index) state, ordinary_fields index⟩

/-- Dynamic PC data for the intended two-iteration execution; this definition
alone asserts no Sail execution, COPY effects, or native trace acceptance. -/
def pathPCs : List (BitVec 32) :=
  [0, 4, 8, 12, 16, 20, 128, 132, 136, 140, 128, 132, 136, 140, 144, 152]

/-- State constructors describe actual primitive Sail updates. -/
def prepare (state : State) (pc : BitVec 32) : State :=
  { state with regs := state.regs.insert .nextPC pc }
def finish (state : State) (pc : BitVec 32) : State :=
  { state with regs := state.regs.insert .PC pc }
def destination (state : State) (reg : SailRV32.Register)
    (value : SailRV32.RegisterType reg) : State :=
  { state with regs := state.regs.insert reg value }

/-- The ordinary normal-step rule retains an arbitrary actual jump target. -/
theorem normal {state executed : State} {pc target : BitVec 32}
    (clause : SailRV32.SailM SailRV32.ExecutionResult)
    (current : run (SailRV32.Functions.get_arch_pc ()) state = .ok pc state)
    (execution : run clause (prepare state (pc + 4)) =
      .ok SailRV32.Functions.RETIRE_SUCCESS executed)
    (next : executed.regs.get? .nextPC = some target) :
    run (normalStep clause) state = .ok SailRV32.Functions.RETIRE_SUCCESS (finish executed target) := by
  simp only [normalStep]
  rw [run_bind_of_ok _ _ _ _ _ (initialize_next_pc current)]
  dsimp only [prepare] at execution
  rw [run_bind_of_ok _ _ _ _ _ execution]
  rw [run_bind_of_ok _ _ _ _ _ (tick_pc_run next)]
  rfl

private theorem write_one (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 1) value) state =
      .ok () (destination state .x1 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem write_two (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 2) value) state =
      .ok () (destination state .x2 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem write_five (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 5) value) state =
      .ok () (destination state .x5 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem write_ten (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 10) value) state =
      .ok () (destination state .x10 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem write_eleven (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 11) value) state =
      .ok () (destination state .x11 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

private theorem write_twelve (state : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 12) value) state =
      .ok () (destination state .x12 value) := by
  simp [SailRV32.Functions.wX_bits, SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, destination]
  rfl

noncomputable def afterCounter : State := finish (destination (prepare before 4) .x5 2) 4
noncomputable def afterDestination : State :=
  finish (destination (prepare afterCounter 8) .x10 destinationAddress) 8
noncomputable def afterSource : State :=
  finish (destination (prepare afterDestination 12) .x11 sourceAddress) 12
noncomputable def afterValue : State := finish (destination (prepare afterSource 16) .x2 7) 16
noncomputable def afterSeed : State :=
  finish (wordWriteState (prepare afterValue 20) sourceAddress.toNat 7) 20
noncomputable def afterEntry : State := finish (prepare afterSeed 128) 128

theorem step_counter : run (normalStep (SailRV32.Functions.execute_ITYPE
    2 (.Regidx 0) (.Regidx 5) .ADDI)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS afterCounter := by
  apply normal (pc := 0) (executed := destination (prepare before 4) .x5 2)
  · exact initial_pc
  · have zero : run (SailRV32.Functions.rX_bits (.Regidx 0)) (prepare before (0 + 4)) =
        .ok 0 (prepare before (0 + 4)) := rfl
    simp only [SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ zero, run_bind_of_ok _ _ _ _ _ (write_five _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

theorem step_destination : run (normalStep (SailRV32.Functions.execute_UTYPE
    0x02000 (.Regidx 10) .LUI)) afterCounter =
      .ok SailRV32.Functions.RETIRE_SUCCESS afterDestination := by
  apply normal (pc := 4) (executed := destination (prepare afterCounter 8) .x10 destinationAddress)
  · apply read_register; simp [afterCounter, finish]
  · simp only [SailRV32.Functions.execute_UTYPE, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ (write_ten _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

theorem step_source : run (normalStep (SailRV32.Functions.execute_ITYPE
    32 (.Regidx 10) (.Regidx 11) .ADDI)) afterDestination =
      .ok SailRV32.Functions.RETIRE_SUCCESS afterSource := by
  apply normal (pc := 8) (executed := destination (prepare afterDestination 12) .x11 sourceAddress)
  · apply read_register; simp [afterDestination, finish]
  · have source : run (SailRV32.Functions.rX_bits (.Regidx 10))
        (prepare afterDestination (8 + 4)) = .ok destinationAddress (prepare afterDestination (8 + 4)) := by
      apply read_register
      simp [prepare, afterDestination, finish, destination, Std.ExtDHashMap.get?_insert]
    simp only [SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ source, run_bind_of_ok _ _ _ _ _ (write_eleven _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

theorem step_value : run (normalStep (SailRV32.Functions.execute_ITYPE
    7 (.Regidx 0) (.Regidx 2) .ADDI)) afterSource =
      .ok SailRV32.Functions.RETIRE_SUCCESS afterValue := by
  apply normal (pc := 12) (executed := destination (prepare afterSource 16) .x2 7)
  · apply read_register; simp [afterSource, finish]
  · have zero : run (SailRV32.Functions.rX_bits (.Regidx 0)) (prepare afterSource (12 + 4)) =
        .ok 0 (prepare afterSource (12 + 4)) := rfl
    simp only [SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ zero, run_bind_of_ok _ _ _ _ _ (write_two _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

private theorem configuredCounter : FlatMemoryConfiguration afterCounter :=
  configuration_pc_write (configuration_gpr_write
    (configuration_next_pc_write configuration 4) 5 2 (write_five _ _)) 4
private theorem configuredDestination : FlatMemoryConfiguration afterDestination :=
  configuration_pc_write (configuration_gpr_write
    (configuration_next_pc_write configuredCounter 8) 10 destinationAddress (write_ten _ _)) 8
private theorem configuredSource : FlatMemoryConfiguration afterSource :=
  configuration_pc_write (configuration_gpr_write
    (configuration_next_pc_write configuredDestination 12) 11 sourceAddress (write_eleven _ _)) 12
private theorem configuredValue : FlatMemoryConfiguration afterValue :=
  configuration_pc_write (configuration_gpr_write
    (configuration_next_pc_write configuredSource 16) 2 7 (write_two _ _)) 16

theorem step_seed : run (normalStep (SailRV32.Functions.execute_STORE
    0 (.Regidx 2) (.Regidx 11) 4)) afterValue =
      .ok SailRV32.Functions.RETIRE_SUCCESS afterSeed := by
  apply normal (pc := 16) (executed := wordWriteState (prepare afterValue 20) sourceAddress.toNat 7)
  · apply read_register; simp [afterValue, finish]
  · apply store_word (before := prepare afterValue 20)
      (after := wordWriteState (prepare afterValue 20) sourceAddress.toNat 7)
      (imm := 0) (rs1 := .Regidx 11) (rs2 := .Regidx 2) (value := 7)
    · apply read_register
      simp [prepare, afterValue, finish, destination, Std.ExtDHashMap.get?_insert]
    · have source : run (SailRV32.Functions.rX_bits (.Regidx 11)) (prepare afterValue 20) =
          .ok sourceAddress (prepare afterValue 20) := by
        apply read_register
        simp [prepare, afterValue, afterSource, finish, destination, Std.ExtDHashMap.get?_insert]
      exact virtual_word_write_platform (before := prepare afterValue 20) (source := sourceAddress)
        (configuration_next_pc_write configuredValue 20) (.Regidx 11) 0 source
        (by decide) (ordinaryWordAddress_airbender _) 7
  · simp [wordWriteState, prepare]

/-- Ordinary direct-jump helper; the required CSR read is an actual Sail read. -/
theorem jump_entry {state : State}
    (pc : run (SailRV32.Functions.get_arch_pc ()) state = .ok 20 state)
    (misa : run (SailRV32.readReg .misa) state = .ok 0x40000100 state) :
    run (normalStep (SailRV32.Functions.execute_JAL 108 (.Regidx 0))) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS (finish (prepare state 128) 128) := by
  apply normal (pc := 20) (executed := prepare state 128)
  · exact pc
  · have next : run (SailRV32.Functions.get_next_pc ()) (prepare state (20 + 4)) =
        .ok 24 (prepare state (20 + 4)) := read_register (by simp [prepare])
    have current : run (SailRV32.readReg .PC) (prepare state (20 + 4)) =
        .ok 20 (prepare state (20 + 4)) :=
      read_register_nextPC (20 + 4) (by decide)
        (show run (SailRV32.readReg .PC) state = .ok 20 state from pc)
    have target : (20 : BitVec 32) + SailRV32.Functions.sign_extend (m := 32) (108 : BitVec 21) =
        128 := by decide
    have jumped : run (SailRV32.Functions.jump_to 128) (prepare state (20 + 4)) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (prepare state 128) := by
      simpa only [prepare, nextPC_overwrite] using jump_to_aligned (by decide)
        (read_register_nextPC (20 + 4) (by decide) misa)
    simp only [SailRV32.Functions.execute_JAL]
    rw [run_bind_of_ok _ _ _ _ _ next, run_bind_of_ok _ _ _ _ _ current, target,
      run_bind_of_ok _ _ _ _ _ jumped]
    rfl
  · simp [prepare]

theorem step_entry : run (normalStep (SailRV32.Functions.execute_JAL 108 (.Regidx 0))) afterSeed =
    .ok SailRV32.Functions.RETIRE_SUCCESS afterEntry := by
  apply jump_entry
  · apply read_register; simp [afterSeed, finish]
  · apply read_register
    simpa [afterSeed, afterValue, afterSource, afterDestination, afterCounter,
      finish, prepare, destination, wordWriteState, Std.ExtDHashMap.get?_insert]
      using read_register_iff.mp initial_misa

/-- The initial source word becomes seven by the actual Sail SW before any
COPY invocation. This proves only the six-instruction prefix. -/
theorem prefix_execution :
    run (do let _ ← normalStep (SailRV32.Functions.execute_ITYPE 2 (.Regidx 0) (.Regidx 5) .ADDI)
            let _ ← normalStep (SailRV32.Functions.execute_UTYPE 0x02000 (.Regidx 10) .LUI)
            let _ ← normalStep (SailRV32.Functions.execute_ITYPE 32 (.Regidx 10) (.Regidx 11) .ADDI)
            let _ ← normalStep (SailRV32.Functions.execute_ITYPE 7 (.Regidx 0) (.Regidx 2) .ADDI)
            let _ ← normalStep (SailRV32.Functions.execute_STORE 0 (.Regidx 2) (.Regidx 11) 4)
            normalStep (SailRV32.Functions.execute_JAL 108 (.Regidx 0))) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS afterEntry := by
  rw [run_bind_of_ok _ _ _ _ _ step_counter, run_bind_of_ok _ _ _ _ _ step_destination,
    run_bind_of_ok _ _ _ _ _ step_source, run_bind_of_ok _ _ _ _ _ step_value,
    run_bind_of_ok _ _ _ _ _ step_seed]
  exact step_entry

theorem prefix_source_seven : (Cell.ram sourceAddress).read afterEntry = .ok 7 afterEntry :=
  read_word_frame (before := wordWriteState (prepare afterValue 20) sourceAddress.toNat 7)
    (after := afterEntry) rfl (written_word_read _ _ _)

theorem prefix_configuration : FlatMemoryConfiguration afterEntry :=
  configuration_pc_write (configuration_next_pc_write
    (configuration_pc_write (configuration_word_write
      (configuration_next_pc_write configuredValue 20) sourceAddress.toNat 7) 20) 128) 128

/-- The prefix retains the original JALR configuration by ordinary register
and memory frames; no extra caller-supplied configuration is assumed. -/
theorem prefix_control_configuration :
    run (SailRV32.readReg .misa) afterEntry = .ok 0x40000100 afterEntry ∧
    run (SailRV32.readReg .cur_privilege) afterEntry = .ok .Machine afterEntry ∧
    run (SailRV32.readReg .mseccfg) afterEntry = .ok 0 afterEntry := by
  refine ⟨?_, ?_, ?_⟩
  · apply read_register
    simpa [afterEntry, afterSeed, afterValue, afterSource, afterDestination, afterCounter,
      finish, prepare, destination, wordWriteState, Std.ExtDHashMap.get?_insert]
      using read_register_iff.mp initial_misa
  · apply read_register
    simpa [afterEntry, afterSeed, afterValue, afterSource, afterDestination, afterCounter,
      finish, prepare, destination, wordWriteState, Std.ExtDHashMap.get?_insert]
      using read_register_iff.mp initial_privilege
  · apply read_register
    simpa [afterEntry, afterSeed, afterValue, afterSource, afterDestination, afterCounter,
      finish, prepare, destination, wordWriteState, Std.ExtDHashMap.get?_insert]
      using read_register_iff.mp initial_security

/-- Later integration can reuse these concrete prefix observations. -/
theorem prefix_registers :
    run (SailRV32.Functions.get_arch_pc ()) afterEntry = .ok 128 afterEntry ∧
    (Cell.register 5).read afterEntry = .ok 2 afterEntry ∧
    (Cell.register 10).read afterEntry = .ok destinationAddress afterEntry ∧
    (Cell.register 11).read afterEntry = .ok sourceAddress afterEntry := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply read_register
  all_goals simp [afterEntry, afterSeed, afterValue, afterSource, afterDestination, afterCounter,
    prepare, finish, destination, wordWriteState, Std.ExtDHashMap.get?_insert]

/-- All prefix stores are beyond the public code, and register/PC updates leave
its bytes unchanged. This is a derived source fact, not a native boundary input. -/
theorem prefix_fetch (index : Fin 12) :
    (Cell.ram (codeEntry index).pc).read afterEntry = .ok (codeEntry index).bits afterEntry := by
  apply read_word_frame (before := wordWriteState (prepare afterValue 20) sourceAddress.toNat 7)
    (after := afterEntry) rfl
  apply written_word_disjoint sourceAddress.toNat 7
  · left
    have bound := code_end index
    change (codeEntry index).pc.toNat + 4 ≤ 33554464
    omega
  · exact read_word_frame (before := before) (after := prepare afterValue 20) rfl (fetch index)

/-- AUIPC uses the actual architectural PC 128 on both visits. Its value does
not come from an affine function of the trace row or clock. -/
theorem step_auipc {state : State}
    (pc : run (SailRV32.Functions.get_arch_pc ()) state = .ok 128 state) :
    run (normalStep (SailRV32.Functions.execute_UTYPE 0 (.Regidx 12) .AUIPC)) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS (finish (destination (prepare state 132) .x12 128) 132) := by
  apply normal (pc := 128) (executed := destination (prepare state 132) .x12 128)
  · exact pc
  · have current : run (SailRV32.Functions.get_arch_pc ()) (prepare state (128 + 4)) =
        .ok 128 (prepare state (128 + 4)) :=
      read_register_nextPC (128 + 4) (by decide)
        (show run (SailRV32.readReg .PC) state = .ok 128 state from pc)
    simp only [SailRV32.Functions.execute_UTYPE, freeM_pure_bind, freeM_bind_assoc]
    rw [run_bind_of_ok _ _ _ _ _ current, run_bind_of_ok _ _ _ _ _ (write_twelve _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

/-- Ordinary decrement, parameterized only by the actual Sail x5 read. This
local semantic premise must be derived from the shared history by integration. -/
theorem step_decrement {state : State} {value : BitVec 32}
    (pc : run (SailRV32.Functions.get_arch_pc ()) state = .ok 136 state)
    (counter : run (SailRV32.Functions.rX_bits (.Regidx 5)) state = .ok value state) :
    run (normalStep (SailRV32.Functions.execute_ITYPE 0xfff (.Regidx 5) (.Regidx 5) .ADDI)) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (finish (destination (prepare state 140) .x5 (value + 0xffffffff)) 140) := by
  apply normal (pc := 136) (executed := destination (prepare state 140) .x5 (value + 0xffffffff))
  · exact pc
  · have source : run (SailRV32.Functions.rX_bits (.Regidx 5)) (prepare state (136 + 4)) =
        .ok value (prepare state (136 + 4)) :=
      rX_nextPC (pc := 136 + 4) (.Regidx 5) counter
    simp only [SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ source, run_bind_of_ok _ _ _ _ _ (write_five _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

theorem step_branch_taken {state : State}
    (pc : run (SailRV32.Functions.get_arch_pc ()) state = .ok 140 state)
    (counter : run (SailRV32.Functions.rX_bits (.Regidx 5)) state = .ok 1 state)
    (misa : run (SailRV32.readReg .misa) state = .ok 0x40000100 state) :
    run (normalStep (SailRV32.Functions.execute_BTYPE 0x1ff4 (.Regidx 0) (.Regidx 5) .BNE)) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS (finish (prepare state 128) 128) := by
  apply normal (pc := 140) (executed := prepare state 128)
  · exact pc
  · have source : run (SailRV32.Functions.rX_bits (.Regidx 5)) (prepare state (140 + 4)) =
        .ok 1 (prepare state (140 + 4)) :=
      rX_nextPC (pc := 140 + 4) (.Regidx 5) counter
    have zero : run (SailRV32.Functions.rX_bits (.Regidx 0)) (prepare state (140 + 4)) =
        .ok 0 (prepare state (140 + 4)) := rfl
    have current : run (SailRV32.readReg .PC) (prepare state (140 + 4)) =
        .ok 140 (prepare state (140 + 4)) :=
      read_register_nextPC (140 + 4) (by decide)
        (show run (SailRV32.readReg .PC) state = .ok 140 state from pc)
    have target : (140 : BitVec 32) + SailRV32.Functions.sign_extend (m := 32) (0x1ff4 : BitVec 13) =
        128 := by decide
    have jumped : run (SailRV32.Functions.jump_to 128) (prepare state (140 + 4)) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (prepare state 128) := by
      simpa only [prepare, nextPC_overwrite] using jump_to_aligned (by decide)
        (read_register_nextPC (140 + 4) (by decide) misa)
    simp only [SailRV32.Functions.execute_BTYPE, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ source, run_bind_of_ok _ _ _ _ _ zero]
    change run (do
      let current ← SailRV32.readReg .PC
      SailRV32.Functions.jump_to
        (current + SailRV32.Functions.sign_extend (m := 32) (0x1ff4 : BitVec 13)))
      (prepare state (140 + 4)) = _
    rw [run_bind_of_ok _ _ _ _ _ current, target]
    exact jumped
  · simp [prepare]

theorem step_branch_untaken {state : State}
    (pc : run (SailRV32.Functions.get_arch_pc ()) state = .ok 140 state)
    (counter : run (SailRV32.Functions.rX_bits (.Regidx 5)) state = .ok 0 state) :
    run (normalStep (SailRV32.Functions.execute_BTYPE 0x1ff4 (.Regidx 0) (.Regidx 5) .BNE)) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS (finish (prepare state 144) 144) := by
  apply normal (pc := 140) (executed := prepare state 144)
  · exact pc
  · have source : run (SailRV32.Functions.rX_bits (.Regidx 5)) (prepare state (140 + 4)) =
        .ok 0 (prepare state (140 + 4)) :=
      rX_nextPC (pc := 140 + 4) (.Regidx 5) counter
    have zero : run (SailRV32.Functions.rX_bits (.Regidx 0)) (prepare state (140 + 4)) =
        .ok 0 (prepare state (140 + 4)) := rfl
    simp only [SailRV32.Functions.execute_BTYPE, freeM_bind_assoc, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ source, run_bind_of_ok _ _ _ _ _ zero]
    rfl
  · simp [prepare]

theorem step_jal {state : State}
    (pc : run (SailRV32.Functions.get_arch_pc ()) state = .ok 144 state)
    (misa : run (SailRV32.readReg .misa) state = .ok 0x40000100 state) :
    run (normalStep (SailRV32.Functions.execute_JAL 8 (.Regidx 1))) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS (finish (destination (prepare state 152) .x1 148) 152) := by
  apply normal (pc := 144) (executed := destination (prepare state 152) .x1 148)
  · exact pc
  · have next : run (SailRV32.Functions.get_next_pc ()) (prepare state (144 + 4)) =
        .ok 148 (prepare state (144 + 4)) := read_register (by simp [prepare])
    have current : run (SailRV32.readReg .PC) (prepare state (144 + 4)) =
        .ok 144 (prepare state (144 + 4)) :=
      read_register_nextPC (144 + 4) (by decide)
        (show run (SailRV32.readReg .PC) state = .ok 144 state from pc)
    have target : (144 : BitVec 32) + SailRV32.Functions.sign_extend (m := 32) (8 : BitVec 21) =
        152 := by decide
    have jumped : run (SailRV32.Functions.jump_to 152) (prepare state (144 + 4)) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (prepare state 152) := by
      simpa only [prepare, nextPC_overwrite] using jump_to_aligned (by decide)
        (read_register_nextPC (144 + 4) (by decide) misa)
    simp only [SailRV32.Functions.execute_JAL]
    rw [run_bind_of_ok _ _ _ _ _ next, run_bind_of_ok _ _ _ _ _ current, target,
      run_bind_of_ok _ _ _ _ _ jumped]
    change run (do
      SailRV32.Functions.wX_bits (.Regidx 1) 148
      pure SailRV32.Functions.RETIRE_SUCCESS) (prepare state 152) = _
    rw [run_bind_of_ok _ _ _ _ _ (write_one _ _)]
    rfl
  · simp [destination, prepare, Std.ExtDHashMap.get?_insert]

/-- Original JALR including the actual landing-pad configuration reads and
low-bit clearing. These ordinary Sail premises are not COPY/native assumptions. -/
theorem step_jalr {state : State}
    (pc : run (SailRV32.Functions.get_arch_pc ()) state = .ok 152 state)
    (link : run (SailRV32.Functions.rX_bits (.Regidx 1)) state = .ok 148 state)
    (misa : run (SailRV32.readReg .misa) state = .ok 0x40000100 state)
    (privilege : run (SailRV32.readReg .cur_privilege) state = .ok .Machine state)
    (security : run (SailRV32.readReg .mseccfg) state = .ok 0 state) :
    run (normalStep (SailRV32.Functions.execute_JALR 8 (.Regidx 1) (.Regidx 0))) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS (finish (prepare state 156) 156) := by
  apply normal (pc := 152) (executed := prepare state 156)
  · exact pc
  · have noPad : run (SailRV32.Functions.update_elp_state (.Regidx 1)) (prepare state (152 + 4)) =
        .ok () (prepare state (152 + 4)) :=
      landing_pad_disabled (.Regidx 1)
        (read_register_nextPC (152 + 4) (by decide) privilege)
        (read_register_nextPC (152 + 4) (by decide) security) (by decide)
    have next : run (SailRV32.Functions.get_next_pc ()) (prepare state (152 + 4)) =
        .ok 156 (prepare state (152 + 4)) := read_register (by simp [prepare])
    have source : run (SailRV32.Functions.rX_bits (.Regidx 1)) (prepare state (152 + 4)) =
        .ok 148 (prepare state (152 + 4)) :=
      rX_nextPC (pc := 152 + 4) (.Regidx 1) link
    have target : ((148 : BitVec 32) + SailRV32.Functions.sign_extend (m := 32) (8 : BitVec 12))
        &&& 0xfffffffe = 156 := by decide
    have jumped : run (SailRV32.Functions.jump_to 156) (prepare state (152 + 4)) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (prepare state 156) := by
      simpa only [prepare, nextPC_overwrite] using jump_to_aligned (by decide)
        (read_register_nextPC (152 + 4) (by decide) misa)
    simp only [SailRV32.Functions.execute_JALR]
    rw [run_bind_of_ok _ _ _ _ _ noPad, run_bind_of_ok _ _ _ _ _ next,
      run_bind_of_ok _ _ _ _ _ source, freeM_pure_bind, clear_bit_zero, target,
      run_bind_of_ok _ _ _ _ _ jumped]
    rfl
  · simp [prepare]

end Tests.DynamicCopyLoopProgram
