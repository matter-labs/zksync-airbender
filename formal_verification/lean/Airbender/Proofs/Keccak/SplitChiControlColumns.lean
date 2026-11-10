import Airbender.Proofs.Keccak.SplitChiPortBindings

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The actual native control-register port. -/
def chi5ControlPort (cached : Bool) : MemoryPort :=
  let ports := (⟨.chi5, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[0]'(by cases cached <;> change 0 < 12 <;> decide)

/-- The native controller lookup contains the actual control-register value limbs. -/
theorem chi5_control_port_columns (cached writing : Bool) (w : Nat → ZMod babyBearModulus) :
    ((if writing then (chi5ControlPort cached).writeValue.getD (chi5ControlPort cached).readValue
      else (chi5ControlPort cached).readValue).evaluate w) =
      #v[(chi5ControllerRow cached w)[if writing then 2 else 0]'(by cases writing <;> decide), w (if writing then 6 else 4)] := by
  cases cached <;> cases writing <;> apply Vector.ext
  all_goals intro i hi
  all_goals have : i = 0 ∨ i = 1 := by omega
  all_goals rcases this with rfl | rfl
  all_goals
    dsimp only [chi5ControlPort, chi5ControllerRow, chi5ControllerQuery, Row.ports,
      Chi5.importedConstraintsMemoryPorts, Chi5Cached.importedConstraintsMemoryPorts,
      Chi5.importedConstraints, Chi5Cached.importedConstraints, WordColumns.evaluate,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment]
  all_goals
    norm_num [Fin.getElem_fin, Expression.eval]

end Airbender.Keccak.Split.Native.Proofs
