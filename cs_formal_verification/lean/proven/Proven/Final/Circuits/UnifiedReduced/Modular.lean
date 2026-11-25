module
public import Proven.UnifiedReduced.Modular.Result
public import Proven.UnifiedReduced.Modular.Soundness
public import Proven.UnifiedReduced.Modular.Witness

@[expose] public section
namespace Airbender.UnifiedReduced.Modular
open Arithmetic AddSub.Modular

/-- The native host uses the two retained BabyBear gates directly in the guest field. -/
theorem babyBear_certificate : ResultCertificate babyBearModulus importedConstraints := by
  intro setup w op holds flags left right old
  obtain ⟨s11, s12, s13, s20, one⟩ := Modular.selected flags
  have s14 := flags 14 (by decide) (by decide)
  have s15 := flags 15 (by decide) (by decide)
  have s16 := flags 16 (by decide) (by decide)
  have s17 := flags 17 (by decide) (by decide)
  refine ⟨Proofs.canonical_output holds s11 s12 s13 s20 one, ?_⟩
  obtain ⟨intermediate, selected⟩ := Proofs.native_equations holds
  have inverse : (4294967296 : ZMod babyBearModulus)⁻¹ = 943718400 := by decide +kernel
  dsimp only [Proofs.lift] at intermediate selected
  cases op <;> simp [Opcode.selector] at s14 s15 s16 s17 <;>
    simp [s14, s15, s16, s17] at intermediate selected <;>
    simp only [arithmeticResult, Word.toBitVec_toNat left, Word.toBitVec_toNat right, Word.toBitVec_toNat old] <;>
    simp [wordAt, Word.value, limbBase, inverse] <;>
    first | linear_combination selected | linear_combination selected - intermediate

/-- Instantiate the common modular theorem with the native BabyBear certificate. -/
theorem babyBear_result : BabyBearResultClaim := soundness babyBear_certificate

theorem babyBear_result_satisfiable : BabyBearResultSatisfiableClaim := Witness.babyBear_satisfiable

end Airbender.UnifiedReduced.Modular
