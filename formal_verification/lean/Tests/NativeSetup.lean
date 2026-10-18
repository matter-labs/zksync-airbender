import Airbender.Proofs.WordMemory.NativeSetup

namespace Tests.NativeSetup
open Airbender Setup WordMemory.Native

/-- The actual native decoder preserves original x0 loads and distinguishes SW. -/
theorem decoder_prefix :
    exportedDecoder.rowNat ⟨0, by decide⟩ = #v[0,0,1,0,3,0,16,0,2,0] ∧
    exportedDecoder.rowNat ⟨1, by decide⟩ = #v[4,0,1,3,0,1,16,0,2,1] ∧
    exportedDecoder.rowNat ⟨2, by decide⟩ = #v[8,0,1,0,0,1,16,0,2,0] := by decide +kernel

/-- UNIMP occurs in ROM as input data, but its actual decoder slot is unsupported. -/
theorem unsupported_word :
    exportedROM.rowNat ⟨3, by decide⟩ = #v[12,4211,49152,24] ∧
    exportedDecoder.rowNat ⟨3, by decide⟩ = Vector.replicate 10 2147483646 := by decide +kernel

/-- Both the public image and original text survive export verbatim. -/
theorem public_words :
    (List.range 4).map exportedImage.get? =
      [some 0x0100a183, some 0x0030a823, some 0x0100a003, some 0xc0001073] ∧
    (List.range 4).map exportedText.get? =
      [some 0x0100a183, some 0x0030a823, some 0x0100a003, some 0xc0001073] := by decide +kernel

theorem separator_boundary :
    exportedSeparator.rowNat ⟨63, by decide⟩ = #v[63,0,63,23] ∧
    exportedSeparator.rowNat ⟨64, by decide⟩ = #v[64,1,0,23] ∧
    exportedSeparator.rowNat ⟨65535, by decide⟩ = #v[65535,1,63,23] := by decide +kernel

/-- Lossless data has an exact endpoint: no implicit zero row is introduced. -/
theorem finite_endpoints : exportedImage.get? 1048576 = none ∧ exportedText.get? 4 = none ∧
    exportedROM.columns[0].get? 1048576 = none := by decide +kernel

end Tests.NativeSetup
