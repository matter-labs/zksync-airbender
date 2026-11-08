import Slop.Trace.Claims

namespace Tests.TraceROM
open Airbender Arithmetic Trace
set_option warningAsError true

private def cells : List Cell := [.register 0, .ram 16]
private def tokens : List (MemoryToken babyBearModulus) :=
  [(Cell.register 0).initialToken 0, (Cell.ram 16).initialToken 0x12345678]

private theorem rows_eq : ROM.rows cells tokens =
    [Vector.replicate 9 0, ROM.row 16 ⟨0x5678, 0x1234⟩] := by
  dsimp [ROM.rows, cells, tokens]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [Trace.Proofs.initial_token_word]
  rfl

theorem native_query : (ROM.table cells tokens).Contains #[]
    #v[16, 0x5678, 0x1234, 0, 0, 0, 0, 0, 34] := by
  have present : (#v[16, 0x5678, 0x1234, 0, 0, 0, 0, 0, 34] : Vector (ZMod babyBearModulus) 9) ∈
      ROM.rows cells tokens := by
    rw [rows_eq]
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr (by decide))
  obtain ⟨i, equal⟩ := List.mem_iff_get.mp present
  exact ⟨i, equal.symm⟩

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

end Tests.TraceROM
