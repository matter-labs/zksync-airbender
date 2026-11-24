module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native Keccak setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks keccakSetup from "artifacts/setup/keccak.json"

end Airbender.Compiler.NativeSetups
