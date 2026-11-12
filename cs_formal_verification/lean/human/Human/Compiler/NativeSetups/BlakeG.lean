module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native blake-g setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks blakeGSetup from "artifacts/setup/blake-g.json"

check_native_ranges "artifacts/setup/blake-g.json"

end Airbender.Compiler.NativeSetups
