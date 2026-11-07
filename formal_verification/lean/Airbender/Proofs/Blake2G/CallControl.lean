import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Trace.Workers.Blake2G.Call
import Airbender.Proofs.Blake2G.Control

namespace Airbender.Blake2G.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem forced_control_step {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {w : Nat → ZMod p} (reduced : Bool) (i : Nat) (bound : i < callCount reduced)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w Variables.execute = 1)
    (current : (w Variables.controlReadLo).val = (controlAt reduced i).lo) :
    Word.mk (w Variables.controlWriteLo).val (w Variables.controlWriteHi).val =
      controlAt reduced (i + 1) := by
  have controlBound : (controlAt reduced i).lo < 256 := by
    cases reduced <;> simp only [controlAt, callCount, Bool.false_eq_true,
      ↓reduceIte] <;> omega
  let input : Control.Input := ⟨⟨(controlAt reduced i).lo, controlBound⟩, true⟩
  let output : Control.Output := ⟨⟨(w Variables.controlWriteLo).val,
    (w Variables.controlWriteHi).val⟩,
    Variables.stateOffsetColumns.map (fun column => (w column).val),
    Variables.messageOffsetColumns.map (fun column => (w column).val)⟩
  have result : output = Control.step input :=
    Control.Proofs.soundness hp input output w ⟨holds, ⟨current.symm, active, rfl⟩⟩
  have update := congrArg Control.Output.register result
  have scheduled : (Control.step input).register = controlAt reduced (i + 1) := by
    cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] at bound
    all_goals interval_cases i
    all_goals rfl'
  exact update.trans scheduled

end Airbender.Blake2G.Proofs
