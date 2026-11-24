module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native bigint setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks bigintSetup from "artifacts/setup/bigint.json"

end Airbender.Compiler.NativeSetups
