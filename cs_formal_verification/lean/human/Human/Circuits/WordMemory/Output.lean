module
public import Human.Helpers.Core.Word

@[expose] public section

/-! The LW/SW circuit's observable outputs: effective address, transferred word and next PC. No Sail import. -/

namespace Airbender.WordMemory
open Airbender.Arithmetic

structure Output where
  address : Word
  data : Word
  pc : Word

end Airbender.WordMemory
