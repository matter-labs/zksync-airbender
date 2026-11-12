module
public import Human.Import.SetupEmit

@[expose] public section

namespace Airbender.Keccak.Split.Chi5

set_option maxRecDepth 400000

/- Native fixed tables of the split Keccak Chi5 worker, read from the exported setup JSON
   (`artifacts/setup/README.md`). Columns are compressed blocks; `decode` is the row value. -/
import_setup_blocks chi5Setup from "artifacts/setup/keccak-chi5.json"

end Airbender.Keccak.Split.Chi5
