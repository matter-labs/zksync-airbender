module
public import Proven.KernelRfl
public import Human.Compiler.Captures.Bigint

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Bigint
/-- The imported capture retains its shared literal placement array. -/
theorem placement_entries : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries = Airbender.Compiler.Captures.Bigint.importedPlacementEntries := by kernel_rfl
end Airbender.Compiler.NativeBindings.Bigint
