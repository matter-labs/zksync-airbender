module
public import Proven.NonVacuous.DynamicCopyLoop.Model
public import Human.Compiler.NativePublicSetup

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler
set_option warningAsError true

/-- Every native CPU lookup group uses the public program and ROM interpretation. -/
noncomputable def tables : ProgramLookupRows := NativePublicSetup.rows initial program

/-- The native setup interpretation meets every public program capacity and projection check. -/
theorem tables_bound : NativePublicSetup.Bound initial program tables := by
  constructor
  · rfl
  · change 12 ≤ 1048576
    decide +kernel
  · intro candidate member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index <;> decide +kernel
  · intro candidate member coordinate
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index <;> fin_cases coordinate <;> decide +kernel

end Airbender.NonVacuous.DynamicCopyLoop
