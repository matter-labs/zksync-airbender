import Airbender.Proofs.Keccak.SplitChiNativeLookup
import Airbender.Review.Trace.Workers.Keccak.SplitNative
import Mathlib.Tactic.ReduceModChar

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- One actual read or write limb from the imported chi5 memory-port descriptors. -/
def chi5LaneLimb (cached writing : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (limb : Fin 4) : ZMod babyBearModulus :=
  let ports := (⟨.chi5, w⟩ : Row babyBearModulus).ports cached
  let port := ports[2 + 2 * lane.val + limb.val / 2]'(by
    have size : ports.size = 12 := by cases cached <;> rfl
    rw [size]
    have := lane.isLt
    have := limb.isLt
    omega)
  let columns := if writing then port.writeValue.getD port.readValue else port.readValue
  (columns.evaluate w)[limb.val % 2]'(Nat.mod_lt _ (by decide))

/-- The nibble value in the actual native arithmetic query. -/
def chi5Nibble (cached writing : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (digit : Fin 16) : ZMod babyBearModulus :=
  (chi5ArithmeticEntry cached digit)[if writing then 5 + lane.val else lane.val]'(by
    have := lane.isLt
    split <;> omega) |>.eval (Verification.environment w)

/-- Every actual native limb equals its four queried nibbles. -/
theorem chi5_lane_packing (cached writing : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (limb : Fin 4) :
    chi5LaneLimb cached writing w lane limb =
      chi5Nibble cached writing w lane ⟨4 * limb.val, by omega⟩ +
        16 * chi5Nibble cached writing w lane ⟨4 * limb.val + 1, by omega⟩ +
        256 * chi5Nibble cached writing w lane ⟨4 * limb.val + 2, by omega⟩ +
        4096 * chi5Nibble cached writing w lane ⟨4 * limb.val + 3, by omega⟩ := by
  cases cached <;> cases writing <;> fin_cases lane <;> fin_cases limb <;>
    dsimp only [chi5LaneLimb, chi5Nibble, Row.ports, WordColumns.evaluate,
      Chi5.importedConstraintsMemoryPorts, Chi5Cached.importedConstraintsMemoryPorts,
      chi5ArithmeticEntry, chi5ArithmeticQuery, Chi5.importedConstraints,
      Chi5Cached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
      Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring_nf <;>
    unfold babyBearModulus at * <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

end Airbender.Keccak.Split.Native.Proofs
