module
public import Human.Import.SetupEmit

@[expose] public section
namespace Airbender.Compiler.NativeSetups
set_option maxRecDepth 65536

/- Native add-sub setup columns. The importer compares every grid region with the exported rows. -/
import_setup_blocks addSubSetup from "artifacts/setup/add-sub.json"


end Airbender.Compiler.NativeSetups
