module
public import Human.Helpers.Core.Word

@[expose] public section

/-! The subword load/store circuit's observable outputs: aligned cell address, transferred word (the extended load
    result, or the merged cell word of a store) and next PC. Shared by the Sail and RV32 statements (no Sail import). -/

namespace Airbender.SubwordMemory
open Airbender.Arithmetic

structure Output where
  cell : Word
  data : Word
  pc : Word

end Airbender.SubwordMemory
