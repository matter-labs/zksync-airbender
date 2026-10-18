import Airbender.Review.Trace.Families.AddSub.NativeDecoder
import Tests.AddSub

namespace Tests.NativeArithmeticSetup
open Airbender Trace Setup AddSub NativeSetup

/-- Constructed from original Sail reads/decoding, with every native row checked. -/
theorem constructed : sparseDecoderSetupImageWith decoderFields before 7 20 = some setup :=
  AddSub.Proofs.native_fixture_image

theorem signed_immediate : arithmeticDecoder.rowNat ⟨1, by decide⟩ =
    #v[4,0,1,0,2,0,65535,65535,0,2] := by decide +kernel

theorem original_x0 : arithmeticDecoder.rowNat ⟨2, by decide⟩ =
    #v[8,0,1,2,0,1,0,0,0,4] ∧ subEntry.instruction =
      .RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .SUB) := by
  exact ⟨by decide +kernel, rfl⟩

theorem raw_upper_fields :
    arithmeticDecoder.rowNat ⟨3, by decide⟩ = #v[12,0,0,0,3,0,28672,0,7,8] ∧
    arithmeticDecoder.rowNat ⟨4, by decide⟩ = #v[16,0,0,0,4,0,20480,0,5,16] := by decide +kernel

theorem hole_and_tail :
    arithmeticDecoder.rowNat ⟨5, by decide⟩ = Vector.replicate 10 2147483646 ∧
    arithmeticDecoder.rowNat ⟨1048575, by decide⟩ = Vector.replicate 10 2147483646 := by decide +kernel

theorem public_text : arithmeticTextWords = 7 ∧
    (List.range 7).map arithmeticText.get? = words.toList.map (some ∘ BitVec.toNat) := by decide +kernel

private def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 39 then 346014073 else Tests.AddSub.row 1 123 123 0 246 0 0 0 24 0 28 0 0 0 i
private def laterRow : Row mersenne31Modulus := ⟨.addSub, assignment⟩

/-- A full native arithmetic row at the original PC after the unsupported hole. -/
theorem later_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment laterRow.assignment) (laterRow.constraints ()) := by
  change FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) AddSub.importedConstraints
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, assignment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem later_source : ∃ entry ∈ setup.program,
    entry.Source before ∧ laterRow.decoderQuery = entry.query :=
  exported_decoder_soundness later_constraints ⟨⟨6, by decide⟩, by decide +kernel⟩

end Tests.NativeArithmeticSetup
