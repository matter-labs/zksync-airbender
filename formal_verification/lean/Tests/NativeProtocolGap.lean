import Airbender.Review.Helpers.Context.ExternalBoundary.HashABI
import Airbender.Proofs.Trace.Values

namespace Tests.NativeProtocolGap
open Airbender Trace Arithmetic
set_option warningAsError true
set_option Elab.async false

/-- The explicit input contract excludes fallback control80. This is a negative
control for the assumption, not a rejection claim about the restored circuit. -/
theorem control80_rejected_by_contract (w : Nat → ZMod babyBearModulus)
    (read : w 3 = 80) : ¬ ExternalBoundary.HashABI.GControl w := by
  rintro ⟨reduced, index, control⟩
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

/-- Equal G block bases violate the explicit separation assumption. No restored
native inverse equation is asserted to enforce this condition. -/
theorem equal_bases_rejected_by_contract (w : Nat → ZMod babyBearModulus)
    (same : (Blake2G.Native.statePointer w).toBitVec =
      (Blake2G.Native.messagePointer w).toBitVec) :
    ¬ ExternalBoundary.HashABI.GBases w := by
  intro separated
  exact separated same

end Tests.NativeProtocolGap
