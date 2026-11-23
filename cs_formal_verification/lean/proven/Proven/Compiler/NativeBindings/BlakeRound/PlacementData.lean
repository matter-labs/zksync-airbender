module
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeRound

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
/-- The imported capture retains its shared literal placement array. -/
theorem placement_entries : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries = Airbender.Compiler.Captures.BlakeRound.importedPlacementEntries := by kernel_rfl
end Airbender.Compiler.NativeBindings.BlakeRound
