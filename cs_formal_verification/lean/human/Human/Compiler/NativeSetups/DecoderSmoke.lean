module
public import Human.Import.SetupEmit
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native decoder-smoke setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks decoderSmokeSetup from "artifacts/setup/decoder-smoke.json"

check_native_ranges "artifacts/setup/decoder-smoke.json"

end Airbender.Compiler.NativeSetups
