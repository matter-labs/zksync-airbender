module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native subword-memory setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks subwordMemorySetup from "artifacts/setup/subword-memory.json"

end Airbender.Compiler.NativeSetups
