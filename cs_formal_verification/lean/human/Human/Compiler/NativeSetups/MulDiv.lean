module
public meta import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- Native setup validation and input tracking. Lake `needs` tracks the JSON;
   `check_native_grid` binds the mathematical rows to the native rows. -/
check_native_setup_input mulDivSetupInput from "artifacts/setup/mul-div.json"

end Airbender.Compiler.NativeSetups
