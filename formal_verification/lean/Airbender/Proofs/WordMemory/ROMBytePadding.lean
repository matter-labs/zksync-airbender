import Airbender.Review.Helpers.Tables.PaddedROMImage
import Airbender.Proofs.Sail.BytePadding
import Airbender.Proofs.WordMemory.ROMImage
import Airbender.Proofs.WordMemory.ROMPadding

namespace Airbender.WordMemory.Proofs
open Arithmetic Verification Trace Reference.RiscV.Sail

/-- Successful actual reads reconstruct the public extractor. Induction is on
    the symbolic extent; even a complete ROM needs no evaluated lookup table. -/
theorem read_rom_words_of_reads {before : State} {count : Nat} (value : Nat → BitVec 32)
    (reads : ∀ i : Fin count, (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok (value i.val) before) :
    readROMWords before count = some (Vector.ofFn fun i => value i.val) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have earlier := ih (fun i => reads ⟨i.val, by omega⟩)
    have last := reads ⟨count, by omega⟩
    unfold readROMWords
    rw [earlier]
    simp only [bind, Option.bind, last, pure]
    congr 1
    ext i
    by_cases bound : i < count
    · simp [bound]
    · have final : i = count := by omega
      simp [final]

/-- Explicit Sail byte padding makes every native ROM word readable with the
    exact zero-padded value. Prefix reads come from the actual public extractor. -/
theorem padded_rom_reads {before : State} {count : Nat} {rom : WordROM}
    (image : wordROMImage before count = some rom) :
    ∀ i : Fin 1048576, (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (paddedROMState before count) =
      .ok (rom.zeroPadded.word i.val) (paddedROMState before count) := by
  obtain ⟨length, reads⟩ := rom_image_reads image
  have bound : count ≤ 1048576 := length ▸ rom.capacity
  intro i
  have address : (BitVec.ofNat 32 (4 * i.val)).toNat = 4 * i.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  by_cases inPrefix : i.val < count
  · rw [zero_padding_prefix rom (by omega)]
    apply padded_rom_word_frame bound (Or.inl (by rw [address]; omega))
    exact reads ⟨i.val, inPrefix⟩
  · rw [zero_padding_tail rom (by omega) i.isLt]
    apply padded_rom_zero_read _ bound <;> rw [address] <;> have := i.isLt <;> omega

/-- Actual word reads recover exactly the supplied finite ROM. The proof keeps
    the extent symbolic, so it does not expand concrete large extractions. -/
theorem rom_image_of_reads {before : State} (rom : WordROM)
    (reads : ∀ i : Fin rom.words.length, (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok (rom.word i.val) before) :
    wordROMImage before rom.words.length = some rom := by
  have extracted := read_rom_words_of_reads _ reads
  unfold wordROMImage
  rw [dif_pos rom.capacity, extracted]
  dsimp only [bind, Option.bind, pure]
  congr 2
  apply List.ext_getElem
  · simp
  · intro i left right
    simp only [Vector.getElem_toList, Vector.getElem_ofFn]
    simp only [WordROM.word, List.getElem?_eq_getElem right, Option.getD_some]

/-- The explicit byte constructor binds the complete four-MiB public ROM, rather
    than postulating padding reads or table equivalence. -/
theorem padded_rom_image {before : State} {count : Nat} {rom : WordROM}
    (image : wordROMImage before count = some rom) :
    wordROMImage (paddedROMState before count) 1048576 = some rom.zeroPadded := by
  have complete := rom_image_of_reads rom.zeroPadded (fun i =>
    padded_rom_reads image ⟨i.val, by simpa only [zero_padding_length] using i.isLt⟩)
  simpa only [zero_padding_length] using complete

/-- Recover the actual prefix construction and explicit padding state from the
    public loader constructor, without supplying expected prefix values. -/
theorem padded_image_source {before after : State} {count : Nat} {rom : WordROM}
    (built : paddedWordROMImage before count = some (after, rom)) :
    ∃ prefixROM, wordROMImage before count = some prefixROM ∧
      after = paddedROMState before count ∧ rom = prefixROM.zeroPadded := by
  unfold paddedWordROMImage at built
  cases image : wordROMImage before count with
  | none => simp [image, bind, Option.bind] at built
  | some prefixROM =>
    simp only [image, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at built
    exact ⟨prefixROM, rfl, built.1.symm, built.2.symm⟩

end Airbender.WordMemory.Proofs
