import Mathlib.Tactic.ReduceModChar
import Airbender.Proofs.Blake2G.SerializedField
import Airbender.Proofs.Blake2Round.NativeFinalQueryDefinitions

namespace Airbender.Blake2Round.Proofs.NativeFinalACBindings
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem columns {p : Nat} [Fact p.Prime] (compatible : SerializedInverse.Scale64 p)
    (w : Nat → ZMod p) (limb : Fin 8) :
    finalColumn w (limb.castLE (by decide)) 0 0 = acTemp w limb 0 ∧
    finalColumn w (limb.castLE (by decide)) 0 1 = acLowC w limb ∧
    finalColumn w (limb.castLE (by decide)) 0 2 = acTemp w limb 1 ∧
    finalColumn w (limb.castLE (by decide)) 1 0 = (-15728640 : ZMod p) * (acInitial w limb - acTemp w limb 0) ∧
    finalColumn w (limb.castLE (by decide)) 1 1 = (-15728640 : ZMod p) * (acC w limb - acLowC w limb) ∧
    finalColumn w (limb.castLE (by decide)) 1 2 = acTemp w limb 2 ∧
    finalColumn w (limb.castLE (by decide)) 2 0 = acTemp w limb 1 ∧
    finalColumn w (limb.castLE (by decide)) 2 1 = acLowA w limb ∧
    finalColumn w (limb.castLE (by decide)) 2 2 = acTemp w limb 4 ∧
    finalColumn w (limb.castLE (by decide)) 3 0 = acTemp w limb 2 ∧
    finalColumn w (limb.castLE (by decide)) 3 1 = (-15728640 : ZMod p) * (acA w limb - acLowA w limb) ∧
    finalColumn w (limb.castLE (by decide)) 3 2 = acTemp w limb 5 := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  fin_cases limb
  all_goals repeat' apply And.intro
  all_goals (simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, acInitial, NativeFinalLayout.initial,
    acTemp, NativeFinalLayout.temporary, acC, NativeFinalLayout.secondInput,
    acLowC, NativeFinalLayout.lowC, acA, NativeFinalLayout.firstInput,
    acLowA, NativeFinalLayout.lowA, diagonalFrame, NativeLayout.diagonal,
    NativeLayout.Layout.read, NativeLayout.Location.read] <;>
      (ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char))


end Airbender.Blake2Round.Proofs.NativeFinalACBindings
