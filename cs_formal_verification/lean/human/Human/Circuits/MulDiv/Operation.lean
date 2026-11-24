module

@[expose] public section
/-! The four unsigned MUL/DIV operations of the circuit and their selector columns. No Sail import. -/

namespace Airbender.MulDiv

inductive Operation where
  | mul | mulhu | divu | remu

end Airbender.MulDiv
