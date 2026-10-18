import Airbender.Review.Helpers.Tables.NativeRowsData
import Airbender.Proofs.Tables.NativeScalars
import Airbender.Proofs.Tables.NativeDecoder
import Airbender.Proofs.WordMemory.PhysicalSetup

namespace Airbender.Verification.NativeSetup.Proofs

theorem compiled_width (kind : DecoderKind) : kind.columns.width = kind.width := by
  cases kind <;> rfl

/-- Every scalar observation uses its actual compiled column. -/
theorem scalar_window (kind : DecoderKind) (rom : WordROM) (row : Row) (scalar : ScalarKind) :
    window kind rom row (scalarColumn kind scalar) 1 = some #v[scalarRow scalar row] := by
  cases kind <;> cases scalar <;>
    dsimp [window, scalarColumn, DecoderKind.columns, DecoderKind.width,
      AddSub.importedConstraintsSetupColumns, WordMemory.importedConstraintsSetupColumns]
  all_goals apply congrArg some
  all_goals apply Vector.ext; intro i bound
  all_goals have zero : i = 0 := by omega
  all_goals subst i; simp [activeRow, arithmeticRow, memoryRow]

/-- The complete decoder tuple follows the generic group in the memory layout. -/
theorem decoder_window (kind : DecoderKind) (rom : WordROM) (row : Row) :
    window kind rom row kind.columns.decoderStart 10 = some (decoderRow kind row) := by
  cases kind <;> dsimp [window, DecoderKind.columns, DecoderKind.width,
    AddSub.importedConstraintsSetupColumns, WordMemory.importedConstraintsSetupColumns]
  all_goals apply congrArg some
  all_goals apply Vector.ext; intro i bound
  all_goals simp [activeRow, arithmeticRow, memoryRow,
    show 2 + i ≠ 1 by omega, show 6 + i ≠ 1 by omega]

/-- Both memory exports have the same native four-column tagged group. -/
theorem generic_window (kind : DecoderKind) (rom : WordROM) (row : Row)
    (present : kind.columns.genericGroups = 1) :
    window kind rom row kind.columns.genericStart 4 = some (genericRow rom row) := by
  cases kind
  · contradiction
  all_goals dsimp [window, DecoderKind.columns, DecoderKind.width,
    WordMemory.importedConstraintsSetupColumns]
  all_goals apply congrArg some
  all_goals apply Vector.ext; intro i bound
  all_goals simp [activeRow, memoryRow,
    show 2 + i ≠ 1 by omega, show 2 + i < 6 by omega]

theorem column_scalar_lookup (kind : DecoderKind) (rom : WordROM) (scalar : ScalarKind)
    (value : ZMod mersenne31Modulus) :
    ColumnLookup kind rom (scalarColumn kind scalar) #v[value] ↔ value.val < 2 ^ scalar.bits := by
  rw [← scalar_lookup scalar value]
  constructor
  · rintro ⟨row, same⟩
    rw [scalar_window] at same
    exact ⟨row, by simpa using congrArg (fun v => v[0]) (Option.some.inj same)⟩
  · rintro ⟨row, same⟩
    exact ⟨row, by rw [scalar_window, same]⟩

theorem column_decoder_lookup (kind : DecoderKind) (rom : WordROM)
    (query : Vector (ZMod mersenne31Modulus) 10) :
    ColumnLookup kind rom kind.columns.decoderStart query ↔ DecoderContains kind query := by
  constructor
  · rintro ⟨row, same⟩
    rw [decoder_window] at same
    exact ⟨row, (Option.some.inj same).symm⟩
  · rintro ⟨row, same⟩
    exact ⟨row, by rw [decoder_window, same]⟩

theorem column_decoder_data (kind : DecoderKind) (rom : WordROM)
    (query : Vector (ZMod mersenne31Modulus) 10) :
    ColumnLookup kind rom kind.columns.decoderStart query ↔
      ∃ i : Fin 1048576, query = decoderPrefixRow kind i :=
  (column_decoder_lookup kind rom query).trans (decoder_membership kind query)

theorem column_tagged_lookup (kind : DecoderKind) (rom : WordROM) (tag : Nat)
    (query : Vector (ZMod mersenne31Modulus) 3) :
    TaggedLookup kind rom tag query ↔ kind.columns.genericGroups = 1 ∧ Contains rom tag query := by
  constructor
  · rintro ⟨present, row, same⟩
    rw [generic_window kind rom row present] at same
    exact ⟨present, row, Option.some.inj same⟩
  · rintro ⟨present, row, same⟩
    exact ⟨present, row, by rw [generic_window kind rom row present, same]⟩

/-- Connect physical scalar columns to the original Clean lookup semantics. -/
theorem column_range16_lookup (kind : DecoderKind) (rom : WordROM)
    {entry : Expression (ZMod mersenne31Modulus)}
    {env : _root_.Environment (ZMod mersenne31Modulus)} :
    ColumnLookup kind rom (scalarColumn kind .range16) #v[entry.eval env] ↔
      (Verification.range16 entry).Contains env := by
  rw [← range16_lookup, column_scalar_lookup, scalar_lookup]

theorem column_timestamp19_lookup (kind : DecoderKind) (rom : WordROM)
    {entry : Expression (ZMod mersenne31Modulus)}
    {env : _root_.Environment (ZMod mersenne31Modulus)} :
    ColumnLookup kind rom (scalarColumn kind .timestamp19) #v[entry.eval env] ↔
      (Verification.timestamp19 entry).Contains env := by
  rw [← timestamp19_lookup, column_scalar_lookup, scalar_lookup]

/-- Typed ROM/separator tags recover the unchanged original Clean fixed tables. -/
theorem column_rom_lookup (kind : DecoderKind) (rom : WordROM)
    (present : kind.columns.genericGroups = 1) (query : Vector (ZMod mersenne31Modulus) 3) :
    TaggedLookup kind rom 24 query ↔ (romWordTable rom).Contains #[] query := by
  rw [column_tagged_lookup, Airbender.WordMemory.Proofs.physical_rom_lookup]
  exact and_iff_right present

theorem column_separator_lookup (kind : DecoderKind) (rom : WordROM)
    (present : kind.columns.genericGroups = 1) (query : Vector (ZMod mersenne31Modulus) 3) :
    TaggedLookup kind rom 23 query ↔ romSeparatorTable.Contains #[] query := by
  rw [column_tagged_lookup, Airbender.WordMemory.Proofs.physical_separator_lookup]
  exact and_iff_right present

end Airbender.Verification.NativeSetup.Proofs
