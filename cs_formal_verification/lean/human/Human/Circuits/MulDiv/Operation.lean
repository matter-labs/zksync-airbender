module

@[expose] public section
/-! The four unsigned MUL/DIV operations of the circuit and their selector columns. No Sail import. -/

namespace Airbender.MulDiv

inductive Operation where
  | mul | mulhu | divu | remu

def Operation.selector : Operation → Fin 4
  | .mul => 0 | .mulhu => 1 | .divu => 2 | .remu => 3

end Airbender.MulDiv
