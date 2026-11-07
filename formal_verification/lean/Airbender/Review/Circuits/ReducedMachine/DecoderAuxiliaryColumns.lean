import Airbender.Review.Circuits.ReducedMachine.AuxiliaryColumns

namespace Airbender.ReducedMachine.Native
/-- Decoder-access quartic geometry, separate from body logical variables. -/
structure DecoderAuxiliaryLayout where
  traceLength : Nat
  extensionOffset : Nat
  width : Nat
  access : Airbender.Blake2Worker.QuarticColumn
  deriving DecidableEq, Inhabited, Repr
end Airbender.ReducedMachine.Native
