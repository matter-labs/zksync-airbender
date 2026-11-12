module
public import Human.Circuits.MulDiv.Operation

/-! Definitions only the proofs use, moved from `human/Human/Circuits/MulDiv/Operation.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.MulDiv
def Operation.selector : Operation → Fin 4
  | .mul => 0 | .mulhu => 1 | .divu => 2 | .remu => 3
end Airbender.MulDiv
