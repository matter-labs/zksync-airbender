import Airbender.Review.Trace.Theorems

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
  change ∃ i : Fin 2, _
  refine ⟨1, ?_⟩
  change _ = (ROM.rows cells tokens).get _
  simp only [List.get_eq_getElem, rows_eq]
  decide

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
  change ¬ ∃ i : Fin 2, _
  change ¬ ∃ i : Fin 2, _ = (ROM.rows cells tokens).get i
  simp only [List.get_eq_getElem, rows_eq]
  decide

theorem missing_address_rejected : ¬ (ROM.table cells tokens).Contains #[]
    #v[20, 0x5678, 0x1234, 0, 0, 0, 0, 0, 34] := by
  change ¬ ∃ i : Fin 2, _
  change ¬ ∃ i : Fin 2, _ = (ROM.rows cells tokens).get i
  simp only [List.get_eq_getElem, rows_eq]
  decide

end Tests.TraceROM
