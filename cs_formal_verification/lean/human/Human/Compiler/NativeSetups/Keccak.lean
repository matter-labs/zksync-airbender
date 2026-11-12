module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native keccak setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks keccakSetup from "artifacts/setup/keccak.json"

check_native_ranges "artifacts/setup/keccak.json"

end Airbender.Compiler.NativeSetups
