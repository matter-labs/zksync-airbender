import Airbender.Proofs.Blake2Round.NativeFinalQueryDefinitions

namespace Airbender.Blake2Round.Proofs.NativeFinalQueryShapes
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem table_eq {p : Nat} [Fact p.Prime] (limb : Fin 16) (stage : Fin 4) :
    (finalQuery (p := p) limb stage).table = setupTable.toRaw := by
  fin_cases limb <;> fin_cases stage <;> rfl

theorem ac_tag {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) (stage : Fin 4) :
    finalColumn w (limb.castLE (by decide)) stage 5 =
      ((#v[19, 20, 19, 20][stage] : Nat) : ZMod p) := by
  fin_cases limb <;> fin_cases stage
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment]

theorem bd_tag {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (limb : Fin 8) (stage : Fin 4) :
    finalColumn w (bdIndex limb) stage 5 = ((#v[20, 19, 4, 4][stage] : Nat) : ZMod p) := by
  fin_cases limb <;> fin_cases stage
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, bdIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment]

end Airbender.Blake2Round.Proofs.NativeFinalQueryShapes
