import Airbender.Proofs.Blake2Round.NativeColumnFacts
import Airbender.Proofs.Blake2Round.NativeGAssignment
import Airbender.Proofs.Blake2G.FrameCarries

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem native_column_flags_complete {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (k : Fin 12) :
    nativeColumnBase call w Blake2G.Variables.booleanColumns[1 + k.val] = 0 ∨
      nativeColumnBase call w Blake2G.Variables.booleanColumns[1 + k.val] = 1 := by
  apply Blake2G.Proofs.Frame.flags_of_bounds (columnFrame call w)
  · intro slot
    have bound := native_column_carries hp call h slot
    fin_cases call <;> fin_cases slot
    all_goals simpa [columnFrame, NativeLayout.column, NativeLayout.columnInputs,
      NativeLayout.Layout.read, NativeLayout.Location.read, columnCarryColumns] using bound
  · intro slot
    have flag := native_column_flags call h slot
    fin_cases call <;> fin_cases slot
    all_goals simpa [columnFrame, NativeLayout.column, NativeLayout.columnInputs,
      NativeLayout.Layout.read, NativeLayout.Location.read, columnBooleanColumns] using flag

end Airbender.Blake2Round.Proofs
