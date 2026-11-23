module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native BLAKE2 G setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks blakeGSetup from "artifacts/setup/blake-g.json"

end Airbender.Compiler.NativeSetups
