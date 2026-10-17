import Airbender.Review.Trace.Families.WordMemory.ROMImage

namespace Tests.WordROMImage
open Airbender Verification Arithmetic Trace

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with mem :=
    (Std.ExtHashMap.emptyWithCapacity |>.insert 0 (0x83 : BitVec 8)
      |>.insert 1 0xa1 |>.insert 2 0 |>.insert 3 0) }
private def rom : WordROM := ⟨[0x0000a183], by decide⟩

private theorem bytes : (Cell.ram 0).read before = .ok (0x0000a183 : BitVec 32) before := by
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
    EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]

private theorem image : wordROMImage before 1 = some rom := by
  have extracted : readROMWords before 1 = some #v[(0x0000a183 : BitVec 32)] := by
    change (match (Cell.ram 0).read before with
      | .ok value _ => some #v[value]
      | .error _ _ => none) = _
    rw [bytes]
  unfold wordROMImage
  rw [dif_pos (by decide), extracted]
  rfl

private def row (i : Nat) : ZMod mersenne31Modulus :=
  if i = 2 then 4
  else if i = 4 ∨ i = 5 ∨ i = 49 ∨ i = 52 ∨ i = 55 then 1
  else if i = 7 then 3
  else if i = 11 then 2
  else if i = 13 then 4
  else if i = 15 then 8
  else if i = 24 then 1
  else if i = 26 ∨ i = 37 ∨ i = 39 ∨ i = 41 then 41347
  else if i = 32 then 1
  else if i = 33 then 3
  else if i = 43 then 1227138194
  else if i = 45 then 2147450879
  else 0

private theorem native :
    FlatOperation.ConstraintsHoldFlat (environment row) (WordMemory.importedConstraints rom) := by
  simp [WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, environment, row]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
      romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, row]
    refine ⟨⟨0, by decide⟩, ?_⟩
    norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom] <;> decide

theorem public_native_rom_read :
    (Cell.ram (WordMemory.addressWord row).toBitVec).read before =
      .ok (Word.mk (row 26).val (row 27).val).toBitVec before :=
  WordMemory.public_rom_prefix_read image native (by decide) (by decide)

theorem extracted_prefix : rom.words.length = 1 ∧
    ∀ i : Fin 1, (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok (rom.word i.val) before := WordMemory.Proofs.rom_image_reads image

theorem native_tail_retained : rom.word 1 = BitVec.ofNat 32 3221229683 ∧
    rom.word 1048575 = BitVec.ofNat 32 3221229683 := ⟨rfl, rfl⟩

private def missing : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with mem := Std.ExtHashMap.emptyWithCapacity }

theorem missing_rom_bytes_rejected : wordROMImage missing 1 = none := by
  simp [wordROMImage, readROMWords, Cell.read, _root_.Sail.ArchSem.readBytes,
    _root_.Sail.ArchSem.readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw, missing]

theorem excessive_count_rejected : wordROMImage before 1048577 = none := rfl

theorem absent_padding_bytes :
    (Cell.ram 4).read before = .error (.OutOfMemoryRange 4) before := by
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, EStateM.bind,
    EStateM.get, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    before]

private def changedData (i : Nat) : ZMod mersenne31Modulus :=
  if i = 26 ∨ i = 37 ∨ i = 39 ∨ i = 41 then 41348 else row i

theorem changed_native_data_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment changedData)
      (WordMemory.importedConstraints rom) := by
  intro accepted
  have read := WordMemory.public_rom_prefix_read image accepted (by decide) (by decide)
  change (Cell.ram 0).read before = .ok (41348 : BitVec 32) before at read
  have different : (41347 : BitVec 32) = 41348 :=
    (EStateM.Result.ok.inj (bytes.symm.trans read)).1
  revert different
  decide

end Tests.WordROMImage
