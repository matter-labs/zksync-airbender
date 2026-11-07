import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.SailWordState
open Airbender.Reference Airbender.Reference.RiscV.Sail
set_option warningAsError true

private def before : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .x1 (9 : BitVec 32)
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 16 (0x78 : BitVec 8)
      |>.insert 17 0x56 |>.insert 18 0x34 |>.insert 19 0x12 }

theorem code_bytes : (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 16).run before =
    .ok (0x12345678 : BitVec 32) before := by
  apply read_word_of_bytes
  intro i
  fin_cases i <;> simp [before, Std.ExtHashMap.getElem_insert]

-- Use the actual native effect, not merely the internal byte-insert normal form.
theorem ram_write_and_read : ∃ after,
    Sail.run (writeMemory (size := 4) 4194304 0x9abcdef0) before = .ok () after ∧
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 4194304).run after =
      .ok (0x9abcdef0 : BitVec 32) after :=
  ⟨_, write_word_state before 4194304 0x9abcdef0,
    written_word_read before 4194304 0x9abcdef0⟩

theorem ram_preserves_code :
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 16).run
      (wordWriteState before 4194304 0x9abcdef0) =
      .ok (0x12345678 : BitVec 32) (wordWriteState before 4194304 0x9abcdef0) :=
  written_word_disjoint 4194304 0x9abcdef0 (Or.inl (by decide)) code_bytes

theorem readonly_state_frame : wordWriteState before 16 0x12345678 = before :=
  written_word_same code_bytes

theorem gpr_preserves_code : ∃ after,
    Sail.run (SailRV32.Functions.wX_bits (.Regidx 1) 27) before = .ok () after ∧
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 16).run after =
      .ok (0x12345678 : BitVec 32) after := by
  obtain ⟨after, written, memory⟩ := gpr_write_memory 1 27 before
  exact ⟨after, written, read_word_frame memory code_bytes⟩

theorem ram_preserves_gpr : Sail.run (SailRV32.Functions.rX_bits (.Regidx 1))
    (wordWriteState before 4194304 0x9abcdef0) =
    .ok (9 : BitVec 32) (wordWriteState before 4194304 0x9abcdef0) := by
  apply rX_register_frame (before := before)
    (after := wordWriteState before 4194304 0x9abcdef0) rfl 1
  apply read_register
  simp [before]

end Tests.SailWordState
