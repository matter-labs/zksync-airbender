module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native subword-memory setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks subwordMemorySetup from "artifacts/setup/subword-memory.json"

check_native_ranges "artifacts/setup/subword-memory.json"

end Airbender.Compiler.NativeSetups
