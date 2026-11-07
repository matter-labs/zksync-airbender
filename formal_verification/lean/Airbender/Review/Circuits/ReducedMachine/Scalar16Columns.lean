import Airbender.Review.Circuits.ReducedMachine.InitializationRangeColumns

namespace Airbender.ReducedMachine.Native
/-- Physical scalar16 multiplicity witness, never a body logical variable. -/
structure Scalar16WitnessColumn where
  index : Nat
  deriving DecidableEq, Inhabited, Repr
/-- Physical scalar16 setup value column, separate from body and auxiliaries. -/
structure Scalar16SetupColumn where
  index : Nat
  deriving DecidableEq, Inhabited, Repr

structure Scalar16Layout where
  traceLength : Nat
  witnessWidth : Nat
  setupWidth : Nat
  extensionOffset : Nat
  width : Nat
  bodyColumns : Vector Nat 8
  bodyProductStart : BaseAuxiliaryColumn
  bodyAccumulatorStart : Airbender.Blake2Worker.QuarticColumn
  initializationProduct : BaseAuxiliaryColumn
  initializationAccumulator : Airbender.Blake2Worker.QuarticColumn
  multiplicity : Scalar16WitnessColumn
  setup : Scalar16SetupColumn
  tableAccumulator : Airbender.Blake2Worker.QuarticColumn
  deriving DecidableEq, Inhabited, Repr
end Airbender.ReducedMachine.Native
