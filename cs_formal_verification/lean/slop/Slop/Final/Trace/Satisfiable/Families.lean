module
public import Slop.NonVacuous.FamilyBoot
public import Slop.NonVacuous.JumpBranchSltTrace
public import Slop.NonVacuous.MulDivTrace
public import Slop.NonVacuous.ShiftBinopTrace
public import Slop.NonVacuous.SubwordMemoryTrace

@[expose] public section

/-! The assumptions of the family trace claims can be met: ADD/SUB + word memory in `Slop/NonVacuous/FamilyBoot.lean`,
    the other families by one row each in `Slop/NonVacuous/<Family>Trace.lean`. -/

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
