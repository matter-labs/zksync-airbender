module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native mul-div setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks mulDivSetup from "artifacts/setup/mul-div.json"


end Airbender.Compiler.NativeSetups
