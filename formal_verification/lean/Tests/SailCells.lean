import Airbender.Proofs.Trace.SailCells

namespace Tests.SailCells
open Airbender Trace Reference Reference.RiscV.Sail
set_option warningAsError true

private def before : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 (9 : BitVec 32)
      |>.insert .x2 (5 : BitVec 32)
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 16 (0x78 : BitVec 8)
      |>.insert 17 0x56 |>.insert 18 0x34 |>.insert 19 0x12 }

private theorem read_x2 : (Cell.register 2).read before = .ok 5 before := by
  apply read_register
  simp [before]

private theorem read_ram : (Cell.ram 16).read before = .ok 0x12345678 before := by
  apply read_word_of_bytes
  intro i
  fin_cases i <;> simp [before, Std.ExtHashMap.getElem_insert]

-- A register write followed by a RAM write keeps both earlier register results,
-- the other register and the preexisting ROM word, through actual Sail effects.
theorem interleaved_native_writes : ∃ middle after,
    Sail.run ((Cell.register 1).write 27) before = .ok () middle ∧
    Sail.run ((Cell.ram 4194304).write 0xabcdef01) middle = .ok () after ∧
    (Cell.register 1).read after = .ok 27 after ∧
    (Cell.register 2).read after = .ok 5 after ∧
    (Cell.ram 16).read after = .ok 0x12345678 after ∧
    (Cell.ram 4194304).read after = .ok 0xabcdef01 after := by
  obtain ⟨middle, regWrite, regRead⟩ := Proofs.cell_write_readback (.register 1) 27 before
    (by intro impossible; cases impossible)
  have otherRead := Proofs.cell_write_frame regWrite (by decide) trivial trivial read_x2
  have codeRead := Proofs.cell_write_frame regWrite (by decide) trivial (by dsimp [Cell.Aligned]) read_ram
  obtain ⟨after, ramWrite, ramRead⟩ := Proofs.cell_write_readback (.ram 4194304)
    0xabcdef01 middle (by intro impossible; cases impossible)
  exact ⟨middle, after, regWrite, ramWrite,
    Proofs.cell_write_frame ramWrite (by decide) (by dsimp [Cell.Aligned]) trivial regRead,
    Proofs.cell_write_frame ramWrite (by decide) (by dsimp [Cell.Aligned]) trivial otherRead,
    Proofs.cell_write_frame ramWrite (by decide) (by dsimp [Cell.Aligned]) (by dsimp [Cell.Aligned]) codeRead, ramRead⟩

theorem refreshed_register_stutters :
    Sail.run ((Cell.register 2).write 5) before = .ok () before :=
  Proofs.cell_write_same read_x2

theorem zero_register_readback : ∃ after,
    Sail.run ((Cell.register 0).write 0) before = .ok () after ∧
    (Cell.register 0).read after = .ok 0 after :=
  Proofs.cell_write_readback (.register 0) 0 before (fun _ => rfl)

theorem nonzero_x0_readback_rejected : ¬ ∃ after,
    Sail.run ((Cell.register 0).write 1) before = .ok () after ∧
    (Cell.register 0).read after = .ok 1 after := by
  rintro ⟨after, _, read⟩
  change EStateM.Result.ok (0 : BitVec 32) after = .ok 1 after at read
  have impossible := (EStateM.Result.ok.inj read).1
  contradiction

-- Distinct byte addresses alone do not justify a word-memory frame.
theorem overlapping_word_frame_rejected : ¬ (Cell.ram 18).read
    (wordWriteState before 16 0x11111111) =
    .ok 0x00001234 (wordWriteState before 16 0x11111111) := by
  intro read
  have originalByte := read_word_memory read (⟨0, by decide⟩ : Fin 4)
  have writtenByte := written_word_byte before 16 0x11111111 (⟨2, by decide⟩ : Fin 4)
  have impossible := originalByte.symm.trans writtenByte
  change some (0x34 : BitVec 8) = some 0x11 at impossible
  contradiction

end Tests.SailCells
