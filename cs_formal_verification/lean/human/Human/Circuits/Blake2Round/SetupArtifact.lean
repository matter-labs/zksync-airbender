module
public import Human.Import.SetupEmit

@[expose] public section

namespace Airbender.Blake2Round

/- Native fixed tables of the six-column round, read from the exported setup JSON
   (`artifacts/setup/README.md`). Columns are compressed blocks; `decode` is the row value. -/
import_setup_blocks blake2RoundSetup from "artifacts/setup/blake-round.json"


end Airbender.Blake2Round
