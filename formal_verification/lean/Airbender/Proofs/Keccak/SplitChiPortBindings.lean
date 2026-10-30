import Airbender.Proofs.Keccak.SplitChiControllerQuery
import Airbender.Proofs.Keccak.SplitChiLaneOperation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- One actual native lane port in JSON order. -/
def chi5LanePort (cached : Bool) (lane : Fin 5) (high : Bool) : MemoryPort :=
  let ports := (⟨.chi5, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[2 + 2 * lane.val + if high then 1 else 0]'(by
    have size : ports.size = 12 := by cases cached <;> rfl
    rw [size]
    have := lane.isLt
    split <;> omega)

/-- The two actual pointer limbs read through register eleven. -/
def chi5Pointer (cached : Bool) (w : Nat → ZMod babyBearModulus) : Vector (ZMod babyBearModulus) 2 :=
  let ports := (⟨.chi5, w⟩ : Row babyBearModulus).ports cached
  let port := ports[1]'(by cases cached <;> change 1 < 12 <;> decide)
  port.readValue.evaluate w

/-- Native memory values retain their exact four-limb lane positions. -/
theorem chi5_lane_port_values (cached writing high : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) :
    (if writing then (chi5LanePort cached lane high).writeCode w
      else (chi5LanePort cached lane high).readCode w) =
      Nat.pair (chi5LaneLimb cached writing w lane (if high then 2 else 0)).val
        (chi5LaneLimb cached writing w lane (if high then 3 else 1)).val := by
  cases cached <;> cases writing <;> cases high <;> fin_cases lane <;> rfl

/-- Native indirect addresses use the controller's physical slot and both pointer limbs. -/
theorem chi5_lane_port_address (cached high : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) :
    (chi5LanePort cached lane high).address.code w = Nat.pair 1
      (Nat.pair ((chi5Pointer cached w)[0] + 8 * (chi5ControllerRow cached w)[3 + lane.val] +
        (if high then 4 else 0 : ZMod babyBearModulus)).val (chi5Pointer cached w)[1].val) := by
  cases cached <;> cases high <;> fin_cases lane <;>
    dsimp [chi5LanePort, chi5Pointer, chi5ControllerRow, chi5ControllerQuery,
      Row.ports, Chi5.importedConstraintsMemoryPorts, Chi5Cached.importedConstraintsMemoryPorts,
      Chi5.importedConstraints, Chi5Cached.importedConstraints, MemoryAddress.code,
      Verification.IndirectPort.rawAddress, WordColumns.evaluate, FlatOperation.lookups,
      List.get, Expression.eval, Verification.environment] <;>
    simp [Expression.eval]

end Airbender.Keccak.Split.Native.Proofs
