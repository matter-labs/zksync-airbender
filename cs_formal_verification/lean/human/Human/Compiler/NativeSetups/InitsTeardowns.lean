module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native inits-and-teardowns setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks initsTeardownsSetup from "artifacts/setup/inits-and-teardowns.json"

check_native_ranges "artifacts/setup/inits-and-teardowns.json"

end Airbender.Compiler.NativeSetups
