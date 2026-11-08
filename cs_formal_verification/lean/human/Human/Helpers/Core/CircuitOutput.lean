module
public import Human.Helpers.Core.Word

@[expose] public section

/-! Observable outputs of the arithmetic circuits: destination word and next PC. Neutral (no Sail import). -/

namespace Airbender.Circuit
open Arithmetic

/-- Observable circuit outputs; all other architectural state is checked through the ISA semantics. -/
structure Output where
  destination : Word
  pc : Word

end Airbender.Circuit
