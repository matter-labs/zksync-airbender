module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native jump-branch setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks jumpBranchSetup from "artifacts/setup/jump-branch.json"


end Airbender.Compiler.NativeSetups
