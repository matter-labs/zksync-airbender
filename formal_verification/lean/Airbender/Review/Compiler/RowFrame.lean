import Airbender.Import.Schema

namespace Airbender.Compiler

/-- A captured row's explicit interpretation boundary. Native arithmetic alone
is not enough: the canonical source frame, helper bounds, authored lookup
membership and execution mask are separate premises. Concrete addresses and
predicates are bound to captured artifacts in Import/Compiler/Rows. -/
structure RowFrame {F S C I : Type}
    (inputAddress : I → GKRAddress)
    (assigned : (S → F) → (C → F) → I → F)
    (arithmeticHolds helperBounds : (GKRAddress → F) → Prop)
    (lookupValid : (S → F) → Prop) (enabled : (GKRAddress → F) → Prop) where
  sourceValue : S → F
  counts : C → F
  physical : GKRAddress → F
  frame : ∀ wire, physical (inputAddress wire) = assigned sourceValue counts wire
  arithmetic : arithmeticHolds physical
  helpers : helperBounds physical
  authored : lookupValid sourceValue
  active : enabled physical

end Airbender.Compiler
