import Airbender.Review.Helpers.Decoder.ArithmeticSparse
import Airbender.Review.Helpers.Tables.NativeDecoder
import Airbender.Proofs.AddSub.NativeSetup
import Airbender.Proofs.WordMemory.NativeSparseSetup

namespace Airbender.Trace.Proofs
open Verification

/-- Accepted source recovery can use the full active decoder domain, without
    supplying a padding-exclusion or table-equivalence premise. -/
theorem active_arithmetic_decoded {trace : Data mersenne31Modulus}
    (decoded : ∀ row ∈ trace.rows,
      NativeSetup.DecoderContains .arithmetic row.decoderQuery) :
    AddSub.SparseDecoded trace AddSub.NativeSetup.setup := by
  intro row member
  obtain ⟨i, same⟩ := (NativeSetup.native_decoder_membership _ _).mp (decoded row member)
  exact ⟨i, same.trans (AddSub.Proofs.native_exported_rows i)⟩

theorem active_word_memory_decoded {trace : Data mersenne31Modulus WordMemoryFamily}
    (decoded : ∀ row ∈ trace.rows,
      NativeSetup.DecoderContains .wordMemoryHoles row.decoderQuery) :
    WordMemory.SparseDecoded trace WordMemory.NativeSparse.setup := by
  intro row member
  obtain ⟨i, same⟩ := (NativeSetup.native_decoder_membership _ _).mp (decoded row member)
  exact ⟨i, same.trans (WordMemory.Proofs.sparse_exported_rows i)⟩

end Airbender.Trace.Proofs
