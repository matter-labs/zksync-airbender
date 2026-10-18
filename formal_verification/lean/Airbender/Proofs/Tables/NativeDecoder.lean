import Airbender.Review.Helpers.Tables.NativeDecoderData

namespace Airbender.Verification.NativeSetup.Proofs

/-- Checked literal output of the same native API called by physical setup. -/
theorem decoder_padding_value : decoderPadding.map (Nat.cast : Nat → ZMod mersenne31Modulus) =
    Vector.replicate 10 (-1) := by decide +kernel

/-- Every actual regional export already contains the native padding sentinel. -/
theorem decoder_padding_in_prefix (kind : DecoderKind) :
    decoderPrefixRow kind ⟨1048575, by decide⟩ = decoderPadding.map Nat.cast := by
  cases kind <;> decide +kernel

theorem decoder_active_prefix (kind : DecoderKind) (i : Fin 1048576) :
    decoderRow kind ⟨i.val, by have := i.isLt; omega⟩ = decoderPrefixRow kind i := by
  simp [decoderRow, i.isLt]

/-- All 15,728,639 remaining active rows use the sentinel, not zero tuples. -/
theorem decoder_active_tail (kind : DecoderKind) (row : Row) (tail : 1048576 ≤ row.val) :
    decoderRow kind row = Vector.replicate 10 (-1) := by
  rw [decoderRow, dif_neg (by omega)]
  exact decoder_padding_value

/-- Repeated active padding adds no query: it is already in every actual native
    prefix. Membership equivalence is proved from literal data, never assumed. -/
theorem decoder_membership (kind : DecoderKind) (query : Vector (ZMod mersenne31Modulus) 10) :
    DecoderContains kind query ↔ ∃ i : Fin 1048576, query = decoderPrefixRow kind i := by
  constructor
  · rintro ⟨row, same⟩
    by_cases early : row.val < 1048576
    · refine ⟨⟨row.val, early⟩, ?_⟩
      simpa only [decoderRow, dif_pos early] using same
    · refine ⟨⟨1048575, by decide⟩, ?_⟩
      rw [decoder_padding_in_prefix]
      simpa only [decoderRow, dif_neg early] using same
  · rintro ⟨i, same⟩
    exact ⟨⟨i.val, by have := i.isLt; omega⟩, same.trans (decoder_active_prefix kind i).symm⟩

end Airbender.Verification.NativeSetup.Proofs
