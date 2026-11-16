module
public import Proven.KernelRfl
public import Human.Compiler.Captures.Keccak

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Keccak
/-- The imported capture retains its shared literal placement array. -/
theorem placement_entries : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries = Airbender.Compiler.Captures.Keccak.importedPlacementEntries := by kernel_rfl
end Airbender.Compiler.NativeBindings.Keccak
