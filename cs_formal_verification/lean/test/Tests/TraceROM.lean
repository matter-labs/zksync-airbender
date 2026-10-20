import Slop.Trace.Claims
import Slop.Trace.CodeHistory

namespace Tests.TraceROM
open Airbender Arithmetic Trace
set_option warningAsError true

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 16 (0x78 : BitVec 8)
      |>.insert 17 0x56 |>.insert 18 0x34 |>.insert 19 0x12 }

private def cells : List Cell := [.register 0, .ram 16]
private def tokens : List (MemoryToken babyBearModulus) :=
  [(Cell.register 0).initialToken 0, (Cell.ram 16).initialToken 0x12345678]

private theorem rows_eq : ROM.rows cells tokens =
    [Vector.replicate 9 0, ROM.row 16 ⟨0x5678, 0x1234⟩] := by
  dsimp [ROM.rows, cells, tokens]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [Trace.Proofs.initial_token_word]
  rfl

theorem extracted : initialImage before cells = some tokens := by
  have zero : (Cell.register 0).read before = .ok 0 before := rfl
  have bytes : (Cell.ram 16).read before = .ok 0x12345678 before := by
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, zero, bytes, bind, Option.bind]
  rfl

theorem native_query : (ROM.table cells tokens).Contains #[]
    #v[16, 0x5678, 0x1234, 0, 0, 0, 0, 0, 34] := by
  have present : (#v[16, 0x5678, 0x1234, 0, 0, 0, 0, 0, 34] : Vector (ZMod babyBearModulus) 9) ∈
      ROM.rows cells tokens := by
    rw [rows_eq]
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr (by decide))
  obtain ⟨i, equal⟩ := List.mem_iff_get.mp present
  exact ⟨i, equal.symm⟩

-- The read result is obtained through modeled table membership and public bytes.
theorem actual_bytes : (Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 16).run before =
    .ok (0x12345678 : BitVec 32) before := by
  have read := rom_reads extracted ⟨16, 0⟩ 0x5678 0x1234 (by constructor <;> decide)
    (by decide) native_query
  exact read

theorem disabled_zero : ∀ query, (ROM.table cells tokens).Contains #[] query →
    query[8] = 0 → query[1] = 0 ∧ query[2] = 0 := by
  intro query contains inactive
  exact ROM.Proofs.disabled (by decide) extracted contains inactive

theorem wrong_value_rejected : ¬ (ROM.table cells tokens).Contains #[]
    #v[16, 0x5679, 0x1234, 0, 0, 0, 0, 0, 34] := by
  change ¬ ∃ i : Fin 2, _ = (ROM.rows cells tokens).get i
  rintro ⟨i, equal⟩
  have present : (#v[16, 0x5679, 0x1234, 0, 0, 0, 0, 0, 34] : Vector (ZMod babyBearModulus) 9) ∈
      ROM.rows cells tokens := equal ▸ List.get_mem (ROM.rows cells tokens) i
  rw [rows_eq] at present
  simp only [List.mem_cons] at present
  rcases present with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem missing_address_rejected : ¬ (ROM.table cells tokens).Contains #[]
    #v[20, 0x5678, 0x1234, 0, 0, 0, 0, 0, 34] := by
  change ¬ ∃ i : Fin 2, _ = (ROM.rows cells tokens).get i
  rintro ⟨i, equal⟩
  have present : (#v[20, 0x5678, 0x1234, 0, 0, 0, 0, 0, 34] : Vector (ZMod babyBearModulus) 9) ∈
      ROM.rows cells tokens := equal ▸ List.get_mem (ROM.rows cells tokens) i
  rw [rows_eq] at present
  simp only [List.mem_cons] at present
  rcases present with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- A readonly native refresh preserves the entire uniform table-byte binding. -/
theorem table_after_refresh : ∃ events,
    SailHistory cells events before before ∧
    ROM.Reads before (ROM.table cells tokens) := by
  let event : MemoryAccess :=
    (1, (Cell.ram 16).addressCode, Nat.pair 0x5678 0x1234, Nat.pair 0x5678 0x1234)
  have bytes : (Cell.ram 16).read before = .ok (memoryWord event.2.2.1) before := by
    simpa [event, Cell.read, memoryWord, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
      Arithmetic.limbBase] using actual_bytes
  have history : SailHistory cells [event] before before := by
    apply SailHistory.cons (.nil before) (.ram 16) (by simp [cells]) rfl bytes
    exact Proofs.cell_write_same bytes
  refine ⟨[event], history, Proofs.rom_reads_after_history (by decide) extracted ?_
    history ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · intro actual member _ _ _
    simp only [List.mem_singleton] at member
    subst actual
    rfl

end Tests.TraceROM
