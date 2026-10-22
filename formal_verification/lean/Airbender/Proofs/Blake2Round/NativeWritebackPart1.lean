import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.PhaseProjection
import Airbender.Proofs.Blake2G.FrameNormalization
import Airbender.Proofs.Blake2Round.FrameOutputs
import Airbender.Proofs.Blake2Round.Reference
import Airbender.Review.Circuits.Blake2Round.Mixing
import Airbender.Proofs.Arithmetic.FieldSliceNormalization
import Airbender.Proofs.Blake2G.SerializedField
import Mathlib.Tactic.ReduceModChar

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- A four-word projection checks native writeback wiring. -/
theorem native_writeback_part_1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (w : Nat → ZMod p) (initial : Vector Arithmetic.Word 16) (i : Fin 4) :
    (Preparation.words w Mixing.extendedWrites)[4 * 1 + i.val] =
      (phaseUpdate 1 (phaseUpdate 0 initial (columnOutputs w)) (diagonalOutputs w))[4 * 1 + i.val] := by
  rw [phase_update_initial_irrelevant 1 _ (Vector.replicate 16 ⟨0, 0⟩) _]
  have field := Blake2G.Proofs.serialized_field compatible
  subst p
  unfold babyBearModulus at *
  fin_cases i
  all_goals simp [Preparation.words, Mixing.extendedWrites, phaseUpdate, callUpdate,
    callConstants, Specs.BLAKE3.roundConstants, Blake2G.State.Proofs.update,
    diagonalOutputs, gOutput, nativeDiagonalAssignment,
     Arithmetic.Word.mk.injEq]
  all_goals constructor
  all_goals apply congrArg ZMod.val
  all_goals simp [
    importedConstraints, FlatOperation.lookups, Blake2G.Proofs.Frame.assignment_eq_normalized,
    Blake2G.Proofs.Frame.normalizedAssignment, columnFrame, diagonalFrame,
    diagonalIncoming, NativeLayout.column, NativeLayout.columnInputs,
    NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read,
    NativeLayout.queryColumn, NativeLayout.queryIndex, nativeColumnAssignment,
    Expression.eval, Verification.environment
  ]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char


end Airbender.Blake2Round.Proofs
