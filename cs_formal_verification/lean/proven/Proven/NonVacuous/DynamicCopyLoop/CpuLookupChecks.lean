module
public import Proven.NonVacuous.DynamicCopyLoop.Model
public import Proven.Compiler.CPUWitnesses.Unified.Data

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler
set_option warningAsError true

/-- Every submitted CPU tuple equals its actual public native lookup row. -/
theorem cpu_lookup_check (index : Fin 16) :
    CPUWitnesses.Unified.canonicalCheck initial program (machineAssignment index) = true := by
  fin_cases index <;> kernel_rfl

end Airbender.NonVacuous.DynamicCopyLoop
