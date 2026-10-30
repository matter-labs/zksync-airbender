import Airbender.Review.Trace.Workers.Keccak.SplitNative
import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def nonzeroPort (address : MemoryAddress) : Bool :=
  match address with
  | .constantRegister index => index != 0
  | .indirect _ => true
  | _ => false

/-- Every imported split port accesses a nonzero register or the RAM space.
This fact holds for both cache modes and needs no witness bounds. -/
theorem port_not_zero (cached : Bool) (row : Row p) {port : MemoryPort}
    (member : port ∈ row.ports cached) :
    port.address.code row.assignment ≠ (Cell.register 0).addressCode := by
  have checked : (row.ports cached).toList.all (fun port => nonzeroPort port.address) = true := by
    cases row with
    | mk kind assignment => cases cached <;> cases kind <;> dsimp only [Row.ports] <;> decide +kernel
  have valid := List.all_eq_true.mp checked port (by simpa using member)
  cases address : port.address
  all_goals simp [address, nonzeroPort] at valid
  all_goals first
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair] at valid ⊢
      exact valid
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair]

end Airbender.Keccak.Split.Native.Proofs
