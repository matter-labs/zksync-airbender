import Airbender.Proofs.Keccak.SplitParityReferenceEffect

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- One actual native lane port in JSON order. -/
def parityLanePort (cached : Bool) (lane : Fin 6) (high : Bool) : MemoryPort :=
  let ports := (⟨.columnParity, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[2 + 2 * lane.val + if high then 1 else 0]'(by
    have size : ports.size = 14 := by cases cached <;> rfl
    rw [size]
    have := lane.isLt
    split <;> omega)

/-- The two actual pointer limbs read through register eleven. -/
def parityPointer (cached : Bool) (w : Nat → ZMod babyBearModulus) : Vector (ZMod babyBearModulus) 2 :=
  let ports := (⟨.columnParity, w⟩ : Row babyBearModulus).ports cached
  let port := ports[1]'(by cases cached <;> change 1 < 14 <;> decide)
  port.readValue.evaluate w

/-- Native memory values retain their exact four-limb lane positions. -/
theorem parity_lane_port_values (cached writing high : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 6) :
    (if writing then (parityLanePort cached lane high).writeCode w
      else (parityLanePort cached lane high).readCode w) =
      Nat.pair (parityLaneLimb cached writing w lane (if high then 2 else 0)).val
        (parityLaneLimb cached writing w lane (if high then 3 else 1)).val := by
  cases cached <;> cases writing <;> cases high <;> fin_cases lane <;> rfl

/-- Native indirect addresses use the controller's physical slot and both pointer limbs. -/
theorem parity_lane_port_address (cached high : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 6) :
    (parityLanePort cached lane high).address.code w = Nat.pair 1
      (Nat.pair ((parityPointer cached w)[0] + 8 * (parityQueryRow cached w 0)[1 + lane.val] +
        (if high then 4 else 0 : ZMod babyBearModulus)).val (parityPointer cached w)[1].val) := by
  cases cached <;> cases high <;> fin_cases lane <;>
    dsimp [parityLanePort, parityPointer, parityQueryRow, columnParityQueryEntry, columnParityQuery,
      Row.ports, ColumnParity.importedConstraintsMemoryPorts, ColumnParityCached.importedConstraintsMemoryPorts,
      ColumnParity.importedConstraints, ColumnParityCached.importedConstraints, MemoryAddress.code,
      Verification.IndirectPort.rawAddress, WordColumns.evaluate, FlatOperation.lookups,
      List.get, Expression.eval, Verification.environment] <;>
    simp [Expression.eval]

end Airbender.Keccak.Split.Native.Proofs
