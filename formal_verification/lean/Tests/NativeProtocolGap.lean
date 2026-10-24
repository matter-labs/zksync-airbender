import Airbender.Proofs.Blake2G.NativeValidity

namespace Tests.NativeProtocolGap
open Airbender Trace Arithmetic
set_option warningAsError true
set_option Elab.async false

/-- The formerly accepted native fallback control80 is rejected by the actual
new imported circuit, even before initialized-memory reasoning. -/
theorem rejected (w : Nat → ZMod babyBearModulus)
    (active : w 0 = 1) (read : w 3 = 80) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) := by
  intro core
  have bound : (w 3).val < 65536 := by rw [read]; decide
  obtain ⟨reduced, index, control⟩ := Blake2G.Proofs.successful_position core active bound
  have low := congrArg Word.lo control
  norm_num [Trace.Proofs.read_word, Blake2G.importedConstraintsMemoryPorts,
    WordColumns.evaluate, read, ZMod.val_ofNat, babyBearModulus] at low
  cases reduced
  · have indexBound : index.val < 80 := index.isLt
    have same : 80 = index.val := by
      simpa [Blake2G.controlAt, Blake2G.callCount, Nat.mod_eq_of_lt indexBound] using low
    omega
  · have impossible : 80 = 128 + index.val % 56 := by
      simpa [Blake2G.controlAt, Blake2G.callCount] using low
    omega

/-- Equal G block bases cannot be rescued by entering at a nonzero counter. -/
theorem equal_bases_rejected (w : Nat → ZMod babyBearModulus)
    (active : w 0 = 1)
    (bounded : (Blake2G.Native.statePointer w).Bounded ∧
      (Blake2G.Native.messagePointer w).Bounded)
    (same : (Blake2G.Native.statePointer w).toBitVec =
      (Blake2G.Native.messagePointer w).toBitVec) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) := by
  intro core
  exact Blake2G.Proofs.successful_bases core active bounded same

end Tests.NativeProtocolGap
