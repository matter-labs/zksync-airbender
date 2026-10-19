import Airbender.Review.Trace.Families.ShiftBinop.NativeDecoder

namespace Tests.ShiftDecoder
open Airbender Arithmetic Trace ShiftBinop NativeSetup

/-- Actual public bytes and original decoding construct every ordinary form. -/
theorem constructed : sparseDecoderSetupImage before 25 20 = some setup :=
  exported_decoder_fidelity.1

theorem original_decode (i : Fin 25) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards words[i.val]) before =
      .ok instructions[i.val] before := Proofs.native_fixture_decode i

/-- Original x0 forms keep native destination zero flags instead of moving to
    a different family or normalizing away the original opcode. -/
private def x0Index (i : Fin 12) : Fin nativeDecoder.length :=
  ⟨12 + i.val,by change 12 + i.val < 1048576; have := i.isLt; omega⟩

theorem original_x0 (i : Fin 12) :
    (nativeDecoder.rowNat (x0Index i))[4] = 0 ∧
    (nativeDecoder.rowNat (x0Index i))[5] = 1 := by
  fin_cases i <;> decide +kernel +revert

/-- Native v2 binary immediates use full sign-extended 16-bit limbs. -/
theorem signed_immediates :
    nativeDecoder.rowNat ⟨9,by decide⟩ = #v[36,0,1,0,3,0,65535,65535,4,40] ∧
    nativeDecoder.rowNat ⟨10,by decide⟩ = #v[40,0,1,0,3,0,63488,65535,6,40] := by
  decide +kernel

/-- SRAI keeps its original encoding's funct7 bits in the native immediate. -/
theorem srai_encoding :
    nativeDecoder.rowNat ⟨8,by decide⟩ = #v[32,0,1,0,3,0,1055,0,5,36] ∧
    nativeDecoder.rowNat ⟨20,by decide⟩ = #v[80,0,1,0,0,1,1055,0,5,36] := by
  decide +kernel

/-- Every actual exported row is connected; no table equality is assumed. -/
theorem all_rows (i : Fin 1048576) :
    nativeDecoder.row (p := mersenne31Modulus) i = setup.row i := exported_decoder_fidelity.2 i

theorem retained_hole_and_tail (i : Fin 1048576) (tail : 24 ≤ i.val) :
    nativeDecoder.rowNat i = Vector.replicate 10 2147483646 := Proofs.native_exported_tail i tail

/-- V3-only REV8 and out-of-profile RV32 shift payloads are not promoted. -/
theorem unsupported : ShiftBinop.decoderFields (.REV8 (.Regidx 1,.Regidx 3)) = none ∧
    ShiftBinop.decoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,.SLLI)) = none ∧
    ShiftBinop.decoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,.SRLI)) = none ∧
    ShiftBinop.decoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,.SRAI)) = none := by exact ⟨rfl,rfl,rfl,rfl⟩

theorem actual_text : nativeTextWords = 25 ∧
    (List.range 25).map nativeText.get? = words.toList.map (some ∘ BitVec.toNat) := by
  decide +kernel

end Tests.ShiftDecoder
