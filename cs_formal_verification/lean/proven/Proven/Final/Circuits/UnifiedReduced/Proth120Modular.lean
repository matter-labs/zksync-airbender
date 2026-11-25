module
public import Proven.UnifiedReduced.Proth120.ModularBounds
public import Proven.UnifiedReduced.Modular.Quotient
public import Proven.UnifiedReduced.Modular.Soundness

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Arithmetic

/-- Quotient equations and lookup bounds recover the guest residue inside Proth120. -/
theorem result_certificate : Modular.ResultCertificate proth120Modulus importedConstraints := by
  intro setup w op holds flags left right old
  obtain ⟨s11, s12, s13, s20, one⟩ := Modular.selected flags
  have s14 := flags 14 (by decide) (by decide)
  have s15 := flags 15 (by decide) (by decide)
  have s16 := flags 16 (by decide) (by decide)
  have s17 := flags 17 (by decide) (by decide)
  have canonical := modular_canonical holds
    s11 s12 s13 s20 one
  have prod := Verification.assertion_of_holds holds ⟨1, by rw [constraint_count]; decide⟩
  have gate := Verification.assertion_of_holds holds ⟨2, by rw [constraint_count]; decide⟩
  op_index at prod gate
  simp [Expression.eval, Verification.environment] at prod gate
  have bit0 := modular_bits holds 1
  have bit1 := modular_bits holds 2
  have bit2 := modular_bits holds 3
  change (w 54).val ≤ 1 at bit0
  change (w 55).val ≤ 1 at bit1
  change (w 56).val ≤ 1 at bit2
  refine ⟨canonical, ?_⟩
  refine Modular.Quotient.row_residue (host := proth120Modulus) (by decide) op _ _ _ _ left right old canonical
    (qLow := (wordAt w 57).value) (qHigh := (w 54).val + 2 * (w 55).val + 4 * (w 56).val)
    (Word.value_lt (modular_ranges holds).2.2) (by omega) (scratch := w 78) ?_ ?_
  · cases op <;> simp [AddSub.Modular.Opcode.selector] at s16 s17 <;>
      simp [wordAt, Word.value, limbBase, s16, s17] at prod ⊢ <;> linear_combination prod
  · cases op <;> simp [AddSub.Modular.Opcode.selector] at s14 s15 s16 s17 <;>
      simp [wordAt, Word.value, limbBase, s14, s15, s16, s17] at gate ⊢ <;> linear_combination gate

/-- Instantiate the common modular theorem with the nonnative quotient certificate. -/
theorem modular_result : ModularResultClaim := Modular.soundness result_certificate

end Airbender.UnifiedReduced.Proth120
