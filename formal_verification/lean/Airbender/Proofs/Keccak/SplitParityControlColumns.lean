import Airbender.Proofs.Keccak.SplitParityPortBindings

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The actual native control-register port. -/
def parityControlPort (cached : Bool) : MemoryPort :=
  let ports := (⟨.columnParity, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[0]'(by cases cached <;> change 0 < 14 <;> decide)

/-- The native controller lookup contains the actual control-register value limbs. -/
theorem parity_control_port_columns (cached writing : Bool) (w : Nat → ZMod babyBearModulus) :
    ((if writing then (parityControlPort cached).writeValue.getD (parityControlPort cached).readValue
      else (parityControlPort cached).readValue).evaluate w) =
      #v[(parityQueryRow cached w 1)[if writing then 2 else 0]'(by cases writing <;> decide), w (if writing then 6 else 4)] := by
  cases cached <;> cases writing <;> apply Vector.ext
  all_goals intro i hi
  all_goals have : i = 0 ∨ i = 1 := by omega
  all_goals rcases this with rfl | rfl
  all_goals
    dsimp only [parityControlPort, parityQueryRow, columnParityQueryEntry, columnParityQuery, Row.ports,
      ColumnParity.importedConstraintsMemoryPorts, ColumnParityCached.importedConstraintsMemoryPorts,
      ColumnParity.importedConstraints, ColumnParityCached.importedConstraints, WordColumns.evaluate,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment]
  all_goals
    norm_num [Fin.getElem_fin, Expression.eval]

end Airbender.Keccak.Split.Native.Proofs
