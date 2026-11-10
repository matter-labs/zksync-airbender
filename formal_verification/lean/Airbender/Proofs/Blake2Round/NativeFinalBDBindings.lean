import Mathlib.Tactic.ReduceModChar
import Airbender.Proofs.Blake2G.SerializedField
import Airbender.Proofs.Blake2Round.NativeFinalQueryDefinitions

namespace Airbender.Blake2Round.Proofs.NativeFinalBDBindings
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem columns {p : Nat} [Fact p.Prime] (compatible : SerializedInverse.Scale64 p)
    (w : Nat → ZMod p) (limb : Fin 8) :
    finalColumn w (bdIndex limb) 0 0 = bdLowB w limb ∧
    finalColumn w (bdIndex limb) 0 1 = bdTemp w limb 0 ∧
    finalColumn w (bdIndex limb) 0 2 = bdTemp w limb 1 ∧
    finalColumn w (bdIndex limb) 1 0 = bdHighB w limb ∧
    finalColumn w (bdIndex limb) 1 1 = (-3932160 : ZMod p) * (bdInitial w limb - bdTemp w limb 0) ∧
    finalColumn w (bdIndex limb) 1 2 = bdTemp w limb 2 ∧
    finalColumn w (bdIndex limb) 2 0 = bdLowD w limb ∧
    finalColumn w (bdIndex limb) 2 1 = bdTemp w limb 1 - 256 * bdTemp w limb 3 ∧
    finalColumn w (bdIndex limb) 2 2 = bdTemp w limb 4 ∧
    finalColumn w (bdIndex limb) 3 0 = bdHighD w limb ∧
    finalColumn w (bdIndex limb) 3 1 = 2 * bdTemp w limb 2 + bdTemp w limb 3 ∧
    finalColumn w (bdIndex limb) 3 2 = bdTemp w limb 5 := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  fin_cases limb
  all_goals repeat' apply And.intro
  all_goals (simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, bdIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, bdInitial, NativeFinalLayout.initial,
    bdTemp, NativeFinalLayout.temporary, bdLowB, NativeFinalLayout.lowB,
    bdHighB, bdB, NativeFinalLayout.firstInput, bdLowD, NativeFinalLayout.lowD,
    bdHighD, bdD, NativeFinalLayout.secondInput, diagonalFrame, NativeLayout.diagonal,
    NativeLayout.Layout.read, NativeLayout.Location.read] <;>
      ring_nf)

end Airbender.Blake2Round.Proofs.NativeFinalBDBindings
