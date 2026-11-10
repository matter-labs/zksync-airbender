import Airbender.Review.Compiler.RowFrame
import Airbender.Review.Compiler.Arithmetic
import Airbender.Review.Compiler.LookupOperands
import Airbender.Review.Compiler.Setup

namespace Airbender.Compiler

/-- Interpret a retained Clean column by its checked physical native address.
The imported address map supplies data; this function supplies the meaning. -/
def physicalAssignment {F : Type} (address : Nat → GKRAddress)
    (physical : GKRAddress → F) : Nat → F := physical ∘ address

end Airbender.Compiler
