import Airbender.Review.Helpers.Tables.NativeRows
import Airbender.Review.Helpers.Context.Model

namespace Airbender.Trace.Proofs
open Verification

/-- Recover complete decoder membership from physical row columns, including
    the native active tail. The arithmetic layout has no ROM/generic group. -/
theorem physical_arithmetic_decoded {trace : Data mersenne31Modulus}
    (decoded : ∀ row ∈ trace.rows,
      NativeSetup.ColumnLookup .arithmetic ⟨[], by decide⟩
        NativeSetup.DecoderKind.arithmetic.columns.decoderStart row.decoderQuery) :
    ∀ row ∈ trace.rows, NativeSetup.DecoderContains .arithmetic row.decoderQuery := by
  intro row member
  exact (NativeSetup.Proofs.column_decoder_lookup _ _ _).mp (decoded row member)

end Airbender.Trace.Proofs
