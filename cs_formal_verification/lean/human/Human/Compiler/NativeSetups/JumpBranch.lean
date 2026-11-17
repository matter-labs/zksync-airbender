module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native jump/branch setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks jumpBranchSetup from "artifacts/setup/jump-branch.json"

end Airbender.Compiler.NativeSetups
