import Human.Helpers.Core.Word

/-! The LW/SW circuit's observable outputs: effective address, transferred word and next PC. Shared by the Sail and
    RV32 statements (no Sail import). -/

namespace Airbender.WordMemory
open Airbender.Arithmetic

structure Output where
  address : Word
  data : Word
  pc : Word

end Airbender.WordMemory
