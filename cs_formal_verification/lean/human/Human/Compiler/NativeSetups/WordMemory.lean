module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native word-memory setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks wordMemorySetup from "artifacts/setup/word-memory.json"

check_native_ranges "artifacts/setup/word-memory.json"

end Airbender.Compiler.NativeSetups
