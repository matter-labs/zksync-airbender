import Airbender.Review.Helpers.Tables.WordROMImage
import Airbender.Review.Circuits.WordMemory.Model
import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.WordMemory.Tables
import Airbender.Proofs.Trace.Program
import Airbender.Proofs.Trace.CodeHistory

namespace Airbender.WordMemory.Proofs
open Arithmetic Verification Trace

/-- Every extracted word is an actual original Sail read preserving the state. -/
theorem read_rom_words {before : Reference.RiscV.Sail.State} {count : Nat}
    {words : Vector (BitVec 32) count} (image : readROMWords before count = some words) :
    ∀ i : Fin count, (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok words[i.val] before := by
  induction count with
  | zero => intro i; exact i.elim0
  | succ count ih =>
    unfold readROMWords at image
    cases previous : readROMWords before count with
    | none => simp [previous, bind, Option.bind] at image
    | some extracted =>
      cases read : (Cell.ram (BitVec.ofNat 32 (4 * count))).read before with
      | error error after => simp [previous, read, bind, Option.bind] at image
      | ok value after =>
        have frame := Trace.Proofs.cell_read_frame _ read
        subst after
        simp only [previous, read, bind, Option.bind, pure, Option.some.injEq] at image
        subst words
        intro i
        by_cases earlier : i.val < count
        · simpa [Vector.getElem_push, earlier] using ih previous ⟨i.val, earlier⟩
        · have last : i.val = count := by omega
          simpa [last, Vector.getElem_push] using read

/-- The constructed prefix is bound to the actual public state; native padding
    remains in the ROM but receives no unproved Sail read guarantee. -/
theorem rom_image_reads {before : Reference.RiscV.Sail.State} {count : Nat} {rom : WordROM}
    (image : wordROMImage before count = some rom) :
    rom.words.length = count ∧ ∀ i : Fin count,
      (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before = .ok (rom.word i.val) before := by
  unfold wordROMImage at image
  split at image
  · cases built : readROMWords before count with
    | none => simp [built, bind, Option.bind] at image
    | some words =>
      simp only [built, bind, Option.bind, pure, Option.some.injEq] at image
      subst rom
      refine ⟨by simp, ?_⟩
      intro i
      have read := read_rom_words built i
      simpa [WordROM.word, List.getElem?_eq_getElem] using read
  · cases image

/-- Native ROM lookup data at an address inside the extracted public prefix.
    The remaining native padding rows are retained without assuming their bytes. -/
theorem native_rom_prefix_read {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {before : Reference.RiscV.Sail.State} {count : Nat} {rom : WordROM} {w : Nat → ZMod p}
    (image : wordROMImage before count = some rom)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (inside : ((w 19).val + 65536 * ((w 20).val % 64)) / 4 < count) :
    (Cell.ram (BitVec.ofNat 32
      (4 * (((w 19).val + 65536 * ((w 20).val % 64)) / 4)))).read before =
      .ok (Word.mk (w 26).val (w 27).val).toBitVec before := by
  obtain ⟨_, low, high⟩ := rom_values hp native
  have canonical := Trace.Proofs.word_of_pc_query
    (pc := rom.word (((w 19).val + 65536 * ((w 20).val % 64)) / 4))
    (by dsimp [limbBase]; omega) low high
  have read := (rom_image_reads image).2 ⟨_, inside⟩
  rw [canonical, Word.ofBitVec_roundtrip]
  exact read

/-- In the native ROM region, the unconditional shadow query is the effective address. -/
theorem rom_query_address {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (region : (addressWord w).hi < 64) :
    BitVec.ofNat 32 (4 * (((w 19).val + 65536 * ((w 20).val % 64)) / 4)) =
      (addressWord w).toBitVec := by
  have aligned := (rom_values hp native).1
  change (w 20).val < 64 at region
  change BitVec.ofNat 32 (4 * (((w 19).val + 65536 * ((w 20).val % 64)) / 4)) =
    BitVec.ofNat 32 ((w 19).val + 65536 * (w 20).val)
  rw [Nat.mod_eq_of_lt region]
  congr 1
  omega

/-- Actual original Sail bytes for a native ROM address in the extracted prefix. -/
theorem native_rom_read {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {before : Reference.RiscV.Sail.State} {count : Nat} {rom : WordROM} {w : Nat → ZMod p}
    (image : wordROMImage before count = some rom)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (region : (addressWord w).hi < 64) (within : (addressWord w).value < 4 * count) :
    (Cell.ram (addressWord w).toBitVec).read before =
      .ok (Word.mk (w 26).val (w 27).val).toBitVec before := by
  have inside : ((w 19).val + 65536 * ((w 20).val % 64)) / 4 < count := by
    change (w 20).val < 64 at region
    change (w 19).val + 65536 * (w 20).val < 4 * count at within
    rw [Nat.mod_eq_of_lt region]
    omega
  have read := native_rom_prefix_read hp image native inside
  rw [rom_query_address hp native region] at read
  exact read

/-- A complete extracted four-MiB image discharges prefix coverage for every
    native ROM address, without an individual expected-read premise. -/
theorem native_full_rom_read {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {before : Reference.RiscV.Sail.State} {rom : WordROM} {w : Nat → ZMod p}
    (image : wordROMImage before 1048576 = some rom)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (region : (addressWord w).hi < 64) :
    (Cell.ram (addressWord w).toBitVec).read before =
      .ok (Word.mk (w 26).val (w 27).val).toBitVec before := by
  apply native_rom_read hp image native region
  have bounds := address_bounds native
  change (w 20).val < 64 at region
  change (w 19).val + 65536 * (w 20).val < 4 * 1048576
  omega

/-- Reuse the extracted-prefix recursion in a later state whose ROM bytes agree.
    No ROM vector is recomputed by evaluation or postulated by a table premise. -/
theorem read_rom_words_after_frame {before after : Reference.RiscV.Sail.State}
    (bytes : ∀ key < 4194304, after.mem[key]? = before.mem[key]?)
    {count : Nat} (bound : count ≤ 1048576) {words : Vector (BitVec 32) count}
    (image : readROMWords before count = some words) :
    readROMWords after count = some words := by
  induction count with
  | zero => simp only [readROMWords] at image ⊢; exact image
  | succ count ih =>
    unfold readROMWords at image ⊢
    cases previous : readROMWords before count with
    | none => simp [previous, bind, Option.bind] at image
    | some extracted =>
      have earlier := ih (by omega) previous
      cases read : (Cell.ram (BitVec.ofNat 32 (4 * count))).read before with
      | error error state => simp [previous, read, bind, Option.bind] at image
      | ok value state =>
        have same := Trace.Proofs.cell_read_frame _ read
        subst state
        have within : (BitVec.ofNat 32 (4 * count)).toNat + 4 ≤ 4194304 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have later := Trace.Proofs.word_read_byte_frame bytes within read
        simpa only [previous, earlier, read, later, bind, Option.bind] using image

/-- Every successful public ROM extraction survives actual byte preservation,
    including the full image. Absent padding bytes stay absent. -/
theorem rom_image_after_frame {before after : Reference.RiscV.Sail.State}
    (bytes : ∀ key < 4194304, after.mem[key]? = before.mem[key]?)
    {count : Nat} {rom : WordROM} (image : wordROMImage before count = some rom) :
    wordROMImage after count = some rom := by
  by_cases bound : count ≤ 1048576
  · unfold wordROMImage at image ⊢
    simp only [dif_pos bound] at image ⊢
    cases built : readROMWords before count with
    | none => simp [built, bind, Option.bind] at image
    | some words =>
      have later := read_rom_words_after_frame bytes bound built
      simpa only [built, later] using image
  · simp [wordROMImage, bound] at image

end Airbender.WordMemory.Proofs
