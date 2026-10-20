import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Circuits.ShiftBinop.Artifact

namespace Airbender.Trace
set_option autoImplicit false

/-- Checked native registry for ordinary shift/binop decoding and initialized logical
    history. Original Sail shift/binop execution remains a separate connection. -/
inductive ShiftBinopFamily where
  | shiftBinop
  deriving DecidableEq

instance : CircuitLayout ShiftBinopFamily where
  columns | .shiftBinop => ShiftBinop.importedConstraintsTraceColumns
  ports | .shiftBinop => ShiftBinop.importedConstraintsMemoryPorts
  decoderColumns | .shiftBinop => ShiftBinop.importedConstraintsDecoderColumns
  constraints | .shiftBinop, _ => ShiftBinop.importedConstraints

end Airbender.Trace
