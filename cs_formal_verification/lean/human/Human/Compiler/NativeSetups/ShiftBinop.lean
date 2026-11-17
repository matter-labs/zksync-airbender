module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- The native shift/binary setup, imported as data. Lake `needs` tracks the JSON. -/
import_setup_blocks shiftBinopSetup from "artifacts/setup/shift-binop.json"

end Airbender.Compiler.NativeSetups
