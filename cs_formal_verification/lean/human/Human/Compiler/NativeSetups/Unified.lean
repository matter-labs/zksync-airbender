module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native unified setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks unifiedSetup from "artifacts/setup/unified.json"

check_native_ranges "artifacts/setup/unified.json"

end Airbender.Compiler.NativeSetups
