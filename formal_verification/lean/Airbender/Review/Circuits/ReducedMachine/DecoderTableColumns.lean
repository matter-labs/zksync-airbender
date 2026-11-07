import Airbender.Review.Circuits.ReducedMachine.DecoderAuxiliaryColumns

namespace Airbender.ReducedMachine.Native
/-- Physical base witness column, with no coercion to body logical variables. -/
structure DecoderWitnessColumn where
  index : Nat
  deriving DecidableEq, Inhabited, Repr
/-- Physical setup column, separate from witness/body and quartic columns. -/
structure DecoderSetupColumn where
  index : Nat
  deriving DecidableEq, Inhabited, Repr

structure DecoderTableLayout where
  traceLength : Nat
  witnessWidth : Nat
  setupWidth : Nat
  decoderCapacity : Nat
  extensionOffset : Nat
  width : Nat
  multiplicity : DecoderWitnessColumn
  setupStart : Nat
  access : Airbender.Blake2Worker.QuarticColumn
  tableMultiplicity : Airbender.Blake2Worker.QuarticColumn
  deriving DecidableEq, Inhabited, Repr
end Airbender.ReducedMachine.Native
