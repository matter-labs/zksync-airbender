import Airbender.Review.Circuits.Blake2Worker.AuxiliaryColumns

namespace Airbender.ReducedMachine.Native
open Airbender.Blake2Worker

/-- Separate selected main stage2 geometry. Its quartic slot92 is not body
    logical variable92. Reusing the column type transfers no worker semantics. -/
structure CallerAuxiliaryLayout where
  traceLength : Nat
  extensionOffset : Nat
  width : Nat
  request : QuarticColumn
  memory : Array QuarticColumn
  state : QuarticColumn
  masking : QuarticColumn
  initialization : QuarticColumn
  grandProduct : QuarticColumn
  deriving DecidableEq, Inhabited, Repr

end Airbender.ReducedMachine.Native
