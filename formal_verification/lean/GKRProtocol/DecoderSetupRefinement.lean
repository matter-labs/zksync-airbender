import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.ColumnSlices

namespace Airbender.Compiler
open Airbender.Trace.NativeDecoder
set_option warningAsError true

def decoderBaseRow (setup : PackedSetup) (data : Setup.TableData setup.width)
    (row : Fin data.length) : Vector Source.BaseField setup.width :=
  (data.row row).map (fun n : Int => (n : Source.BaseField))

theorem decoder_active_tag (query : Vector Source.BaseField 9) : (activeQuery query)[9] = 46 := by
  simp [activeQuery]

/-- The hypotheses are checked against complete imported columns by each
instance. Membership remains the logical lookup-argument boundary. -/
theorem decoder_full_lookup_of_rows (setup : PackedSetup) (data : Setup.TableData setup.width)
    (domain : data.length = setup.offset + setup.realRows.length + setup.padding.length)
    (leadingRows : ∀ row : Fin data.length, row.val < setup.offset →
      setup.tagged = true ∧ (normalizeDecoderFields setup (decoderBaseRow setup data row))[9] =
        (Setup.signedValue ((setup.prefixTags.get? row.val).getD 0) : Source.BaseField))
    (tailRows : ∀ (row : Fin data.length) (outside : ¬row.val < setup.offset),
      normalizeDecoderFields setup (decoderBaseRow setup data row) =
        (setup.row ⟨row.val - setup.offset, by have := row.isLt; omega⟩).map
          (fun n => (Setup.signedValue n : Source.BaseField)))
    (packed : Vector Source.BaseField setup.width) (query : Vector Source.BaseField 9)
    (normalized : normalizeDecoderFields setup packed = activeQuery query)
    (name : String) (member : (data.table name).Contains #[] packed) : setup.lookup query := by
  obtain ⟨row, equal⟩ := member
  change packed = decoderBaseRow setup data row at equal
  have values : activeQuery query = normalizeDecoderFields setup (decoderBaseRow setup data row) :=
    normalized.symm.trans (congrArg (normalizeDecoderFields setup) equal)
  refine ⟨⟨row.val, by rw [← domain]; exact row.isLt⟩, ?_⟩
  by_cases leading : row.val < setup.offset
  · rw [dif_pos leading]
    have parts := leadingRows row leading
    refine ⟨parts.1, ?_⟩
    exact ((decoder_active_tag query).symm.trans
      (congrArg (fun vector : Vector Source.BaseField 10 => vector[9]) values)).trans parts.2
  · rw [dif_neg leading]
    exact values.trans (tailRows row leading)

end Airbender.Compiler
