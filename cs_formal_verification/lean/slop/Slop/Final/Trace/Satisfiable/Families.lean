module
public import Slop.NonVacuous.FamilyBoot

@[expose] public section

/-! The assumptions of the ADD/SUB + word-memory trace claims can be met: `Slop/NonVacuous/FamilyBoot.lean`. -/

namespace Airbender.Trace
open NonVacuous.FamilyBoot

theorem rv_airbender_soundness_satisfiable : RVAirbenderSoundnessSatisfiableClaim :=
  ⟨registerTrace, _, _, _, execution_boundary, accepted _ _, decoded _ _, rows_ne _ _⟩

theorem rv_native_boot_soundness_satisfiable : RVNativeBootSoundnessSatisfiableClaim :=
  ⟨bootTrace, _, _, _, _, boot_boundary, accepted _ _, decoded _ _, rows_ne _ _⟩

end Airbender.Trace
