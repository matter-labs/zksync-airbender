import Airbender.Import.SetupProgramEmbed

namespace Airbender.Trace.ROM
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_program nativeProgramData from "artifacts/setup/word-memory.json"

/-- Architectural words of the complete imported public image. -/
def importedWords (index : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((nativeProgramData.image.get? index).getD 0)

end Airbender.Trace.ROM
