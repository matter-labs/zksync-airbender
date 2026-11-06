import Human.Import.SetupEmit

namespace Airbender.Keccak.Split.ColumnParity

set_option maxRecDepth 400000

/- Native fixed tables of the split Keccak ColumnParity worker, read from the exported setup JSON
   (`artifacts/setup/README.md`). Columns are compressed blocks; `decode` is the row value. -/
import_setup_blocks columnParitySetup from "artifacts/setup/keccak-column-parity.json"

end Airbender.Keccak.Split.ColumnParity
