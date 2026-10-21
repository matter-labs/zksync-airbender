import Airbender.Review.Trace.Families.SubwordMemory.NativeDecoder

namespace Tests.SubwordNativeDecoder
open Airbender Arithmetic Trace SubwordMemory NativeSetup
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem constructed : sparseDecoderSetupImage before 13 20 = some setup :=
  exported_decoder_fidelity.1

theorem original_decode (i : Fin 13) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards words[i.val]) before =
      .ok instructions[i.val] before := Proofs.native_fixture_decode i

theorem all_rows (i : Fin 1048576) :
    nativeDecoder.row (p := mersenne31Modulus) i = setup.row i := exported_decoder_fidelity.2 i

theorem tail (i : Fin 1048576) (outside : 12 ≤ i.val) :
    nativeDecoder.rowNat i = Vector.replicate 10 2147483646 := Proofs.native_exported_tail i outside

theorem signed_zero_loads (i : Fin 4) :
    (nativeDecoder.rowNat ⟨6 + i.val,by change 6 + i.val < 1048576; have := i.isLt; omega⟩)[3] = 0 ∧
    (nativeDecoder.rowNat ⟨6 + i.val,by change 6 + i.val < 1048576; have := i.isLt; omega⟩)[4] = 0 ∧
    (nativeDecoder.rowNat ⟨6 + i.val,by change 6 + i.val < 1048576; have := i.isLt; omega⟩)[5] = 1 ∧
    (nativeDecoder.rowNat ⟨6 + i.val,by change 6 + i.val < 1048576; have := i.isLt; omega⟩)[6] = 65535 ∧
    (nativeDecoder.rowNat ⟨6 + i.val,by change 6 + i.val < 1048576; have := i.isLt; omega⟩)[7] = 65535 := by
  fin_cases i <;> decide +kernel +revert

/-- Negative S-type raw bits contain rd=31, which the actual decoder clears. -/
theorem negative_stores : nativeDecoder.rowNat ⟨10,by decide⟩ = #v[40,0,1,2,0,1,65535,65535,0,1] ∧
    nativeDecoder.rowNat ⟨11,by decide⟩ = #v[44,0,1,2,0,1,65535,65535,1,1] := by decide +kernel

theorem actual_text : nativeTextWords = 13 ∧
    (List.range 13).map nativeText.get? = words.toList.map (some ∘ BitVec.toNat) := by decide +kernel

end Tests.SubwordNativeDecoder
