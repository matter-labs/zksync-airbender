module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native add/sub setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks addSubSetup from "artifacts/setup/add-sub.json"

end Airbender.Compiler.NativeSetups
