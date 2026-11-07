import Airbender.Review.Circuits.ReducedMachine.AuxiliaryColumns

namespace Airbender.ReducedMachine.Native
/-- A base-field stage2 column. No body-variable or quartic coercion exists. -/
structure BaseAuxiliaryColumn where
  index : Nat
  deriving DecidableEq, Inhabited, Repr

/-- Extra native initialization-address pair, separate from the four original
    scalar16 pairs and from subtraction-remainder body queries. -/
structure InitializationRangeLayout where
  traceLength : Nat
  extensionOffset : Nat
  width : Nat
  product : BaseAuxiliaryColumn
  accumulator : Airbender.Blake2Worker.QuarticColumn
  deriving DecidableEq, Inhabited, Repr
end Airbender.ReducedMachine.Native
