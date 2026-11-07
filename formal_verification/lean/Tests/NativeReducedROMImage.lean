import Airbender.Review.Trace.Families.ReducedMachine.ROMImage
import Airbender.Review.Circuits.ReducedMachine.WordMemoryROMTheorems

namespace Tests.NativeReducedROMImage
open Airbender ReducedMachine Native Arithmetic Trace Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Independent exact original word reads for all eight public fixture slots. -/
theorem all_fixture_reads (before : State) (i : Fin 8) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (NativeROM.state before) =
      .ok (#v[(0x001080b3 : BitVec 32),0xfff08113,0x40208033,0x000071b7,
        0x00005217,0x0000a183,0x0020a023,0xc0001073][i.val]) (NativeROM.state before) := by
  have actual := NativeROMProofs.word_read before ⟨i.val,by have := i.isLt; omega⟩
  have values : ∀ j : Fin 8, NativeROM.fixture.word j.val =
      #v[(0x001080b3 : BitVec 32),0xfff08113,0x40208033,0x000071b7,
        0x00005217,0x0000a183,0x0020a023,0xc0001073][j.val] := by decide +kernel
  rw [values i] at actual
  exact actual

/-- Both ends of the actual padding tail are readable UNIMP, not zero. -/
theorem padding_reads (before : State) :
    (Cell.ram 32).read (NativeROM.state before) = .ok (0xc0001073 : BitVec 32) (NativeROM.state before) ∧
    (Cell.ram 4194300).read (NativeROM.state before) = .ok (0xc0001073 : BitVec 32) (NativeROM.state before) := by
  have first := NativeROMProofs.word_read before ⟨8,by decide⟩
  have last := NativeROMProofs.word_read before ⟨1048575,by decide⟩
  have firstValue : NativeROM.fixture.word 8 = (0xc0001073 : BitVec 32) := by decide +kernel
  have lastValue : NativeROM.fixture.word 1048575 = (0xc0001073 : BitVec 32) := by decide +kernel
  rw [firstValue] at first
  rw [lastValue] at last
  exact ⟨first,last⟩

theorem complete_public_extraction (before : State) :
    wordROMImage (NativeROM.state before) 1048576 = some NativeROM.complete :=
  (public_rom_image before).1

theorem original_registers_preserved (before : State) :
    (NativeROM.state before).regs = before.regs := (public_rom_image before).2.2.1

theorem architectural_ram_bytes_preserved (before : State) {key : Nat} (ram : 4194304 ≤ key) :
    (NativeROM.state before).mem[key]? = before.mem[key]? := (public_rom_image before).2.2.2 key ram

/-- The constructor explicitly overwrites ROM bytes even if the input differs. -/
theorem first_byte_constructed (before : State) : (NativeROM.state before).mem[0]? = some (0xb3 : BitVec 8) := by
  rw [NativeROMProofs.state_byte,if_pos (by decide)]
  have value : NativeROM.byte 0 = (0xb3 : BitVec 8) := by decide +kernel
  rw [value]

/-- No shadow123-to-ROM value identity is introduced. -/
theorem shadow_value_independent (before : State) :
    (Cell.ram 16).read (NativeROM.state before) = .ok (21015 : BitVec 32) (NativeROM.state before) ∧
      (123 : BitVec 32) ≠ 21015 := by
  have read := NativeROMProofs.numerical_read before ⟨4,by decide⟩
  exact ⟨read,by decide⟩

private def empty : State := { (default : State) with mem := Std.ExtHashMap.emptyWithCapacity }

/-- Finite construction does not fabricate bytes beyond the native ROM extent. -/
theorem missing_ram_byte_remains_missing : (NativeROM.state empty).mem[4194304]? = none := by
  rw [NativeROMProofs.outside_byte empty (by decide)]
  simp [empty]

/-- A corrupted fixed-ROM output at actual address16 cannot satisfy native LW.
    This is a conditional rejection, not a full positive accepted LW fixture. -/
theorem corrupt_native_rom_value_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus))
    (low : w 61 = 16) (high : w 62 = 0)
    (bad : (⟨(w 66).val,(w 67).val⟩ : Word).toBitVec ≠ 21015) : False := by
  have read := word_load_rom_read empty holds mask (by simp [wordMemoryAddressWord,high])
  have address : (wordMemoryAddressWord w).toBitVec = (16 : BitVec 32) := by
    simp only [wordMemoryAddressWord,Word.toBitVec,Word.value,limbBase,low,high,
      ZMod.val_zero,Nat.mul_zero,Nat.add_zero]
    have numeral : (16 : ZMod mersenne31Modulus).val = 16 := by decide +kernel
    rw [numeral]
    rfl
  rw [address] at read
  have correct := (shadow_value_independent empty).1
  exact bad ((EStateM.Result.ok.inj (read.symm.trans correct)).1)

end Tests.NativeReducedROMImage
