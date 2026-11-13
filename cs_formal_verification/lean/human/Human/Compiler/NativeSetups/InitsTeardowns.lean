module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native inits-and-teardowns setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks initsTeardownsSetup from "artifacts/setup/inits-and-teardowns.json"


end Airbender.Compiler.NativeSetups
