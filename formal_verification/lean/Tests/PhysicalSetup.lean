import Airbender.Review.Trace.Families.WordMemory.Setup

namespace Tests.PhysicalSetup
open Airbender Verification Trace Reference.RiscV.Sail

private def rom : WordROM := ⟨[0x0100a183], by decide⟩
private def before : State :=
  { (default : State) with mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 0 0x83 |>.insert 1 0xa1 |>.insert 2 0 |>.insert 3 1) }
private abbrev initial := paddedROMState before 1

private theorem image : paddedWordROMImage before 1 = some (initial, rom.zeroPadded) := by
  have bytes : (Cell.ram (BitVec.ofNat 32 (4 * 0))).read before = .ok (0x0100a183 : BitVec 32) before := by
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  unfold paddedWordROMImage wordROMImage
  rw [dif_pos (by decide)]
  simp only [readROMWords, bytes, bind, Option.bind, pure]
  rfl

/-- Nonzero original LW bytes occur in the complete tagged physical ROM region. -/
theorem rom_prefix : NativeSetup.Contains rom.zeroPadded 24
    (#v[0, 41347, 256] : Vector (ZMod mersenne31Modulus) 3) := by
  apply (Airbender.WordMemory.Proofs.physical_rom_lookup _ _).mpr
  change ∃ i : Fin 1048576, _ = (rom.zeroPadded.row i).map Nat.cast
  refine ⟨⟨0, by decide⟩, ?_⟩
  have word : rom.zeroPadded.word 0 = 0x0100a183 := by
    rw [Airbender.WordMemory.Proofs.zero_padding_prefix _ (by decide)]
    rfl
  norm_num [WordROM.row, word]
  decide

/-- The next physical ROM slot contains the loader's actual zero word. -/
theorem rom_tail : NativeSetup.Contains rom.zeroPadded 24
    (#v[4, 0, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  apply (Airbender.WordMemory.Proofs.physical_rom_lookup _ _).mpr
  change ∃ i : Fin 1048576, _ = (rom.zeroPadded.row i).map Nat.cast
  refine ⟨⟨1, by decide⟩, ?_⟩
  have word : rom.zeroPadded.word 1 = 0 :=
    Airbender.WordMemory.Proofs.zero_padding_tail _ (by decide) (by decide)
  norm_num [WordROM.row, word]
  decide

/-- Tagged setup membership supplies actual Sail reads of both the original
    instruction word and its explicitly constructed padding, without read premises. -/
theorem actual_rom_reads :
    (Cell.ram 0).read initial = .ok (0x0100a183 : BitVec 32) initial ∧
    (Cell.ram 4).read initial = .ok (0 : BitVec 32) initial := by
  constructor
  · have read := Airbender.WordMemory.physical_setup_rom_read (before := before) (initial := initial)
      (key := 0) (lo := 41347) (hi := 256) image rom_prefix
    simpa [Arithmetic.Word.toBitVec, Arithmetic.Word.value, Arithmetic.limbBase,
      show (0 : ZMod mersenne31Modulus).val = 0 from by decide,
      show (41347 : ZMod mersenne31Modulus).val = 41347 from by decide,
      show (256 : ZMod mersenne31Modulus).val = 256 from by decide] using read
  · have read := Airbender.WordMemory.physical_setup_rom_read (before := before) (initial := initial)
      (key := 4) (lo := 0) (hi := 0) image rom_tail
    simpa [Arithmetic.Word.toBitVec, Arithmetic.Word.value, Arithmetic.limbBase,
      show (4 : ZMod mersenne31Modulus).val = 4 from by decide,
      show (0 : ZMod mersenne31Modulus).val = 0 from by decide] using read

/-- Values from zero dummy/padding tuples cannot authenticate altered ROM data;
    the tag and actual original bytes both remain checked. -/
theorem altered_rom_rejected : ¬NativeSetup.Contains rom.zeroPadded 24
    (#v[0, 0, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have result := Airbender.WordMemory.physical_setup_rom_read (before := before) (initial := initial)
    (key := 0) (lo := 0) (hi := 0) image member
  have changed : (Cell.ram 0).read initial = .ok (0 : BitVec 32) initial := by
    simpa [Arithmetic.Word.toBitVec, Arithmetic.Word.value, Arithmetic.limbBase,
      show (0 : ZMod mersenne31Modulus).val = 0 from by decide] using result
  rw [actual_rom_reads.1] at changed
  have wrong : (0x0100a183 : BitVec 32) = 0 := (EStateM.Result.ok.inj changed).1
  exact (by decide : ¬(0x0100a183 : BitVec 32) = 0) wrong

/-- The native separator row tags are distinct from word-ROM tags. -/
theorem separator_row : NativeSetup.Contains rom.zeroPadded 23
    (#v[64, 1, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  apply (Airbender.WordMemory.Proofs.physical_separator_lookup _ _).mpr
  change ∃ i : Fin 65536, _ = (romSeparatorRow i).map Nat.cast
  exact ⟨⟨64, by decide⟩, by norm_num [romSeparatorRow]⟩

/-- Even a padding tuple with matching first three values has the wrong tag. -/
theorem padding_cannot_supply_rom (row : NativeSetup.Row) (padding : 1114113 ≤ row.val)
    (query : Vector (ZMod mersenne31Modulus) 3) :
    NativeSetup.genericRow rom.zeroPadded row ≠ query.push 24 := by
  intro same
  have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
  rw [Airbender.WordMemory.Proofs.physical_padding_tag _ _ padding] at tag
  exact ((by decide : (0 : ZMod mersenne31Modulus) ≠ 24) (by simpa using tag))

end Tests.PhysicalSetup
