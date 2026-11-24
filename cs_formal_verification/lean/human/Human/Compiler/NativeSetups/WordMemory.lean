module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native word-memory setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks wordMemorySetup from "artifacts/setup/word-memory.json"

end Airbender.Compiler.NativeSetups
