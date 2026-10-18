import Airbender.Review.Helpers.Tables.NativeRows

namespace Tests.NativeRows
open Airbender Verification NativeSetup

private def rom : WordROM := ⟨[0x0100a183], by decide⟩

/-- Layout width and group positions are actual imported compiled metadata. -/
theorem compiled_layouts :
    DecoderKind.arithmetic.columns.width = 12 ∧
    DecoderKind.wordMemory.columns.width = 16 ∧
    DecoderKind.wordMemoryHoles.columns.width = 16 ∧
    DecoderKind.arithmetic.columns.decoderStart = 2 ∧
    DecoderKind.wordMemory.columns.decoderStart = 6 := by decide

/-- A complete query must fit: a truncated window cannot authenticate zeros. -/
theorem truncated_queries_rejected (row : NativeSetup.Row) :
    window .arithmetic rom row 3 10 = none ∧
    window .wordMemory rom row 7 10 = none := by
  constructor <;> simp [window, DecoderKind.width]

/-- Arithmetic has no native generic group, even where four columns fit. -/
theorem absent_generic_rejected (query : Vector (ZMod mersenne31Modulus) 3) :
    ¬TaggedLookup .arithmetic rom 24 query := by
  rintro ⟨impossible, _⟩
  contradiction

/-- Last active rows mix scalar/generic zeros and decoder minus-one sentinels. -/
theorem last_active_row :
    activeRow .arithmetic rom ⟨16777214, by decide⟩ =
      #v[(0 : ZMod mersenne31Modulus), 0] ++ Vector.replicate 10 (-1 : ZMod mersenne31Modulus) ∧
    activeRow .wordMemory rom ⟨16777214, by decide⟩ =
      #v[(0 : ZMod mersenne31Modulus), 0, 0, 0, 0, 0] ++ Vector.replicate 10 (-1 : ZMod mersenne31Modulus) := by
  decide +kernel

/-- This row is decoder filler but still lies inside the tagged ROM region. -/
theorem overlapping_regions :
    window .wordMemory rom ⟨1048576, by decide⟩ 0 1 = some #v[0] ∧
    window .wordMemory rom ⟨1048576, by decide⟩ 1 1 = some #v[0] ∧
    window .wordMemory rom ⟨1048576, by decide⟩ 2 4 =
      some ((rom.row ⟨983039, by decide⟩).map Nat.cast |>.push 24) ∧
    window .wordMemory rom ⟨1048576, by decide⟩ 6 10 =
      some (Vector.replicate 10 (-1)) := by
  have r16 := NativeSetup.Proofs.scalar_padding_zero (p := mersenne31Modulus)
    .range16 ⟨1048576, by decide⟩ (by decide)
  have t19 := NativeSetup.Proofs.scalar_padding_zero (p := mersenne31Modulus)
    .timestamp19 ⟨1048576, by decide⟩ (by decide)
  have decoder := NativeSetup.Proofs.decoder_active_tail .wordMemory ⟨1048576, by decide⟩ (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [r16, scalarColumn, DecoderKind.columns,
      WordMemory.importedConstraintsSetupColumns] using NativeSetup.Proofs.scalar_window .wordMemory rom ⟨1048576, by decide⟩ .range16
  · simpa only [t19, scalarColumn, DecoderKind.columns,
      WordMemory.importedConstraintsSetupColumns] using NativeSetup.Proofs.scalar_window .wordMemory rom ⟨1048576, by decide⟩ .timestamp19
  · have selected := NativeSetup.Proofs.generic_window .wordMemory rom ⟨1048576, by decide⟩ rfl
    simpa [DecoderKind.columns, WordMemory.importedConstraintsSetupColumns, genericRow] using selected
  · simpa only [decoder, DecoderKind.columns,
      WordMemory.importedConstraintsSetupColumns] using NativeSetup.Proofs.decoder_window .wordMemory rom ⟨1048576, by decide⟩

/-- Canonical range endpoint cannot be supplied by any full-row scalar value. -/
theorem scalar_overflow_rejected (kind : DecoderKind) :
    ¬ColumnLookup kind rom (scalarColumn kind .range16) #v[(65536 : ZMod mersenne31Modulus)] := by
  rw [native_row_scalar]
  decide

/-- Scalar and decoder domains retain their different native padding meanings. -/
theorem padding_queries :
    ColumnLookup .arithmetic rom 0 #v[(0 : ZMod mersenne31Modulus)] ∧
    ColumnLookup .arithmetic rom 2 (Vector.replicate 10 (-1)) := by
  constructor
  · exact (native_row_scalar .arithmetic rom .range16 0).mpr (by decide)
  · apply (NativeSetup.Proofs.column_decoder_lookup .arithmetic rom _).mpr
    exact ⟨⟨16777214, by decide⟩,
      (NativeSetup.Proofs.decoder_active_tail _ _ (by decide)).symm⟩

/-- The actual ROM word is recovered from columns 2..5 including native tag 24. -/
theorem original_rom_tuple : TaggedLookup .wordMemory rom 24
    (#v[0, 41347, 256] : Vector (ZMod mersenne31Modulus) 3) := by
  apply (NativeSetup.Proofs.column_rom_lookup .wordMemory rom rfl _).mpr
  change ∃ i : Fin 1048576, _ = (rom.row i).map Nat.cast
  refine ⟨⟨0, by decide⟩, ?_⟩
  norm_num [rom, WordROM.row, WordROM.word]
  decide

/-- Dummy/zero tuples do not manufacture ROM data by dropping the native tag. -/
theorem dummy_wrong_tag (row : NativeSetup.Row) (tail : 1114113 ≤ row.val) :
    window .wordMemory rom row 2 4 ≠ some (#v[0, 0, 0, 24] : Vector (ZMod mersenne31Modulus) 4) := by
  change window .wordMemory rom row DecoderKind.wordMemory.columns.genericStart 4 ≠ _
  rw [NativeSetup.Proofs.generic_window .wordMemory rom row rfl]
  intro same
  have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) (Option.some.inj same)
  rw [Airbender.WordMemory.Proofs.physical_padding_tag rom row tail] at tag
  exact (by decide : (0 : ZMod mersenne31Modulus) ≠ 24) (by simpa using tag)

end Tests.NativeRows
