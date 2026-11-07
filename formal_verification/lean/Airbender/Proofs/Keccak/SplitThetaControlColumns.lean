import Airbender.Proofs.Keccak.SplitThetaPortBindings

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The actual native control-register port. -/
def thetaControlPort (cached : Bool) : MemoryPort :=
  let ports := (⟨.thetaRho, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[0]'(by cases cached <;> change 0 < 16 <;> decide)

/-- The native controller lookup contains the actual control-register value limbs. -/
theorem theta_control_port_columns (cached writing : Bool) (w : Nat → ZMod babyBearModulus) :
    ((if writing then (thetaControlPort cached).writeValue.getD (thetaControlPort cached).readValue
      else (thetaControlPort cached).readValue).evaluate w) =
      #v[(thetaQueryRow cached w 9)[if writing then 2 else 0]'(by cases writing <;> decide), w (if writing then 6 else 4)] := by
  cases cached <;> cases writing <;> apply Vector.ext
  all_goals intro i hi
  all_goals have : i = 0 ∨ i = 1 := by omega
  all_goals rcases this with rfl | rfl
  all_goals
    dsimp only [thetaControlPort, thetaQueryRow, thetaRhoQueryEntry, thetaRhoQuery, Row.ports,
      ThetaRho.importedConstraintsMemoryPorts, ThetaRhoCached.importedConstraintsMemoryPorts,
      ThetaRho.importedConstraints, ThetaRhoCached.importedConstraints, WordColumns.evaluate,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment]
  all_goals
    norm_num [Fin.getElem_fin, Expression.eval]

end Airbender.Keccak.Split.Native.Proofs
