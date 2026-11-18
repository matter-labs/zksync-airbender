module
public import Proven.NonVacuous.DynamicCopyLoop.NativeSource
public import Proven.NonVacuous.DynamicCopyLoop.NativeSetup
public import Proven.NonVacuous.DynamicCopyLoop.CpuLookupChecks
public import Proven.Compiler.CPUWitnesses.Unified

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler
set_option warningAsError true

/-- Every submitted CPU occurrence has native gates, source placement, public lookup matching and participation. -/
noncomputable def cpuCertificate (index : Fin 16) : UnifiedLogicalRowCertificate tables :=
  CPUWitnesses.Unified.of_checked initial program (machineAssignment index)
    (cpu_source_satisfied index) (cpu_lookup_check index) (by rfl)

/-- The full native CPU certificate retains the supplied row and its occurrence. -/
theorem cpuCertificate_row (index : Fin 16) :
    (cpuCertificate index).row = (⟨.machine, machineAssignment index⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) := rfl

end Airbender.NonVacuous.DynamicCopyLoop
