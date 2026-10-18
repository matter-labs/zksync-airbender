import Tests.WordMemory
import Airbender.Review.Trace.Families.WordMemory.SparseExecution

namespace Tests.SparseExecution
open Airbender Verification Arithmetic Trace
open Reference.RiscV.Sail

private def rom : WordROM := ⟨WordMemory.NativeSparse.words.toList ++ [0], by decide⟩
private def nativeRow : Row mersenne31Modulus WordMemoryFamily := ⟨.wordMemory, WordMemory.sparseAfterHole⟩
private def cells : List Cell := [.register 1, .ram 4194320, .register 0]
private def trace : Data mersenne31Modulus WordMemoryFamily where
  rows := [nativeRow]
  rom := rom
  initial := nativeRow.start
  terminal := nativeRow.finish
  initialMemory := [(Cell.register 1).initialToken 4194304,
    (Cell.ram 4194320).initialToken 123, (Cell.register 0).initialToken 0]
  terminalMemory := nativeRow.writes

/-- Every original native equation/lookup and every state/memory token matches;
    the starting PC 12 is public data, after the unsupported word at PC four. -/
theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same : actual = nativeRow := by simpa [trace] using member
    subst actual
    exact Tests.WordMemory.sparse_after_hole_native_constraints (by decide +kernel)
  · intro actual member
    have same : actual = nativeRow := by simpa [trace] using member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · have initial : trace.initialMemory.Perm nativeRow.reads := by decide +kernel
    exact (initial.append_right _).trans List.perm_append_comm

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def before : State :=
  { WordMemory.NativeSparse.before with
    regs := ((Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (4194304 : BitVec 32) |>.insert .PC (12 : BitVec 32)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0) |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes] |>.insert .mhartid 7
      |>.insert .htif_tohost_base none)
    mem := WordMemory.NativeSparse.before.mem
      |>.insert 16 0 |>.insert 17 0 |>.insert 18 0 |>.insert 19 0
      |>.insert 4194320 123 |>.insert 4194321 0 |>.insert 4194322 0 |>.insert 4194323 0 }

private theorem bytes (i : Fin 5) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok (rom.word i.val) before := by
  fin_cases i <;>
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, WordMemory.NativeSparse.before,
      WordMemory.NativeSparse.words, rom, WordROM.word, Std.ExtHashMap.getElem_insert]

/-- Actual byte memory constructs the same sparse native fixture, with all
    original PCs retained. The original decoder certificate is reused unchanged. -/
theorem decoder_built : WordMemory.sparseDecoderSetupImage before 4 20 =
    some WordMemory.NativeSparse.setup := by
  have slots (i : Fin 4) :
      programSlotWith WordMemory.decoderFields before (BitVec.ofNat 32 (4 * i.val)) =
      programSlotWith WordMemory.decoderFields WordMemory.NativeSparse.before
        (BitVec.ofNat 32 (4 * i.val)) := by
    unfold programSlotWith
    rw [bytes ⟨i.val, by omega⟩, WordMemory.Proofs.sparse_fixture_words i]
    have word : rom.word i.val = WordMemory.NativeSparse.words[i.val] := by
      fin_cases i <;> decide +kernel
    rw [word]
  change (([0,4,8,12] : List (BitVec 32)).mapM (programSlotWith WordMemory.decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048572)) = _
  have original := WordMemory.Proofs.sparse_fixture_image
  change (([0,4,8,12] : List (BitVec 32)).mapM
      (programSlotWith WordMemory.decoderFields WordMemory.NativeSparse.before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048572)) = _ at original
  have s0 := slots ⟨0, by decide⟩
  have s1 := slots ⟨1, by decide⟩
  have s2 := slots ⟨2, by decide⟩
  have s3 := slots ⟨3, by decide⟩
  change programSlotWith WordMemory.decoderFields before 0 =
    programSlotWith WordMemory.decoderFields WordMemory.NativeSparse.before 0 at s0
  change programSlotWith WordMemory.decoderFields before 4 =
    programSlotWith WordMemory.decoderFields WordMemory.NativeSparse.before 4 at s1
  change programSlotWith WordMemory.decoderFields before 8 =
    programSlotWith WordMemory.decoderFields WordMemory.NativeSparse.before 8 at s2
  change programSlotWith WordMemory.decoderFields before 12 =
    programSlotWith WordMemory.decoderFields WordMemory.NativeSparse.before 12 at s3
  simpa only [List.mapM_cons, List.mapM_nil, s0, s1, s2, s3] using original

theorem rom_built : wordROMImage before 5 = some rom := by
  unfold wordROMImage
  rw [dif_pos (by decide)]
  simp only [readROMWords, bytes ⟨0, by decide⟩, bytes ⟨1, by decide⟩,
    bytes ⟨2, by decide⟩, bytes ⟨3, by decide⟩, bytes ⟨4, by decide⟩, bind, Option.bind, pure]
  rfl

private theorem inputs : WordMemory.ShadowImageBoundary trace before cells [] := by
  have source : (Cell.register 1).read before = .ok (4194304 : BitVec 32) before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have ramRead : (Cell.ram 4194320).read before = .ok (123 : BitVec 32) before := by
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before = .ok (12 : BitVec 32) before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  constructor
  · decide
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl <;>
      simp [WordMemory.Proofs.architectural_register, WordMemory.Proofs.architectural_ram]
  · simp
  · simp only [WordMemory.shadowInitialImage, cells, initialImage, List.mapM_cons,
      List.mapM_nil, source, ramRead]
    rfl
  · rw [initialState, pc]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem configuration : FlatMemoryConfiguration before := by
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
  · simp [before]

/-- Full membership uses actual exported decoder slot three, after the hole. -/
theorem decoded : WordMemory.SparseDecoded trace WordMemory.NativeSparse.setup := by
  intro actual member
  have same : actual = nativeRow := by simpa [trace] using member
  subst actual
  change ∃ i : Fin 1048576, nativeRow.decoderQuery = WordMemory.NativeSparse.setup.row i
  refine ⟨⟨3, by decide⟩, ?_⟩
  rw [← WordMemory.Proofs.sparse_exported_rows]
  decide +kernel

theorem initialized_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    WordMemory.Realizes WordMemory.NativeSparse.setup.program trace before cells := by
  apply WordMemory.sparse_public_sail_execution inputs decoder_built accepted decoded
    (by intro cell member; simp [cells] at member; rcases member with rfl | rfl | rfl <;> simp [Cell.Aligned])
    configuration rom_built (by decide)
  · intro address member
    have same : address = (4194320 : BitVec 32) := by simpa [cells] using member
    subst address
    unfold OrdinaryWordAddress
    decide
  · simp

/-- Exact terminal PC 16 and the actual discarded x0 write follow from native
    matching and original fetched execution; no read/result/state is an input. -/
theorem terminal_values [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    ∃ after, Relation.ReflTransGen (WordMemory.SailStep WordMemory.NativeSparse.setup.program) before after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after = .ok (16 : BitVec 32) after ∧
      (Cell.ram 4194320).read after = .ok (123 : BitVec 32) after ∧
      (Cell.register 0).read after = .ok (0 : BitVec 32) after := by
  obtain ⟨after, execution, pc, values⟩ := initialized_execution
  have port := values ((writeToken nativeRow.columns nativeRow.assignment nativeRow.ports[1]))
    (by decide +kernel) (by decide +kernel)
  obtain ⟨ramCell, _, address, read⟩ := port
  have same : ramCell = Cell.ram 4194320 := Trace.Proofs.cell_address_injective address
  subst ramCell
  refine ⟨after, execution, pc, ?_, rfl⟩
  have word : (writeToken nativeRow.columns nativeRow.assignment nativeRow.ports[1]).word.toBitVec =
      (123 : BitVec 32) := by decide +kernel
  simpa only [word] using read

end Tests.SparseExecution
