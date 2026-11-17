module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native unified setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks unifiedSetup from "artifacts/setup/unified.json"

end Airbender.Compiler.NativeSetups
