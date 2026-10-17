import Tests.AddSub
import Airbender.Proofs.AddSub.Timestamp

namespace Tests.NativeClocks
open Airbender

private def row := Tests.AddSub.row 1 123 123 0 246 0 0 0 0 0 4 0 0 0

private theorem inputs : Trace.ClockInputs AddSub.importedConstraintsTraceColumns row := by
  constructor
  · constructor <;> decide
  · decide
  · simp [AddSub.importedConstraintsTraceColumns, Trace.decodeTimestamp,
      Trace.Timestamp.Bounded, row, Tests.AddSub.row]

theorem native_order : Trace.ClockEffects AddSub.importedConstraintsTraceColumns row :=
  AddSub.Proofs.clock_effects (by decide) Tests.AddSub.add_satisfies inputs

theorem native_clock_advances : (Trace.decodeTimestamp row
    AddSub.importedConstraintsTraceColumns.finalTime).value = 8 := by
  have initial : (Trace.decodeTimestamp row
      AddSub.importedConstraintsTraceColumns.initialTime).value = 4 := by decide
  simpa only [initial] using native_order.advances

end Tests.NativeClocks
