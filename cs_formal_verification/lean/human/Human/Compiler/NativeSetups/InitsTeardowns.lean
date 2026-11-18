module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native inits/teardowns setup, imported as data. It has no generic lookup columns; Lake `needs` tracks the
   JSON. -/
import_setup_blocks initsTeardownsSetup from "artifacts/setup/inits-and-teardowns.json"

end Airbender.Compiler.NativeSetups
