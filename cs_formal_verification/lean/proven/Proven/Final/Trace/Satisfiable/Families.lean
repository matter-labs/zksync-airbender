module
public import Proven.NonVacuous.FamilyBoot
public import Proven.NonVacuous.JumpBranchSltTrace
public import Proven.NonVacuous.MulDivTrace
public import Proven.NonVacuous.ShiftBinopTrace
public import Proven.NonVacuous.SubwordMemoryTrace

@[expose] public section

/-! The assumptions of the family trace claims can be met: ADD/SUB + word memory in `Proven/NonVacuous/FamilyBoot.lean`,
    the other families by one row each in `Proven/NonVacuous/<Family>Trace.lean`. -/

namespace Airbender.Trace
open NonVacuous.FamilyBoot

theorem rv_airbender_soundness_satisfiable : RVAirbenderSoundnessSatisfiableClaim :=
  ⟨registerTrace, _, _, _, execution_boundary, accepted _ _, decoded _ _, rows_ne _ _⟩

theorem rv_native_boot_soundness_satisfiable : RVNativeBootSoundnessSatisfiableClaim :=
  ⟨bootTrace, _, _, _, _, boot_boundary, accepted _ _, decoded _ _, rows_ne _ _⟩

end Airbender.Trace

namespace Airbender.JumpBranchSlt
open NonVacuous.JumpBranchSltTrace

theorem rv_trace_soundness_satisfiable : RVTraceSoundnessSatisfiableClaim :=
  ⟨trace, initial, cells, program, inputs, accepted, decoded, List.cons_ne_nil _ _⟩

end Airbender.JumpBranchSlt

namespace Airbender.MulDiv
open NonVacuous.MulDivTrace

theorem rv_trace_soundness_satisfiable : RVTraceSoundnessSatisfiableClaim :=
  ⟨trace, initial, cells, program, inputs, accepted, decoded, List.cons_ne_nil _ _⟩

end Airbender.MulDiv

namespace Airbender.ShiftBinop
open NonVacuous.ShiftBinopTrace

theorem rv_trace_soundness_satisfiable : RVTraceSoundnessSatisfiableClaim :=
  ⟨trace, initial, cells, program, inputs, accepted, decoded, List.cons_ne_nil _ _⟩

end Airbender.ShiftBinop

namespace Airbender.SubwordMemory
open NonVacuous.SubwordMemoryTrace

theorem rv_ram_trace_soundness_satisfiable : RVRamTraceSoundnessSatisfiableClaim :=
  ⟨trace, initial, cells, program, inputs, accepted, decoded, List.cons_ne_nil _ _⟩

end Airbender.SubwordMemory
