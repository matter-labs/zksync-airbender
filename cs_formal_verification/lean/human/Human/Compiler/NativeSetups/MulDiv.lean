module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native multiply/divide setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks mulDivSetup from "artifacts/setup/mul-div.json"

end Airbender.Compiler.NativeSetups
