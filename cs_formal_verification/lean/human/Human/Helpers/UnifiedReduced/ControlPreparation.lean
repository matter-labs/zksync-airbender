module

@[expose] public section

namespace Airbender.UnifiedReduced.Caller

/-- Instructions that write a public constant from x0 or a U-immediate. -/
inductive ControlLiteral where
  | addi (immediate : BitVec 12)
  | lui (immediate : BitVec 20)

end Airbender.UnifiedReduced.Caller
