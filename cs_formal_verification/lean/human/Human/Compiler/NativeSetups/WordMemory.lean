module
public meta import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- Native setup validation and input tracking. Lake `needs` tracks the JSON;
   `check_native_grid` binds the mathematical rows to the native rows. -/
check_native_setup_input wordMemorySetupInput from "artifacts/setup/word-memory.json"

end Airbender.Compiler.NativeSetups
