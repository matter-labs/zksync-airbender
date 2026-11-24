module
public import Human.Helpers.Delegation.Memory
public import Proven.KernelRfl
public import Proven.OpIndex
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384

private def nonzeroPort (address : MemoryAddress) : Bool :=
  match address with
  | .constantRegister index => index != 0
  | .indirect _ => true
  | _ => false

theorem port_not_zero (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.address.code row.assignment ≠ (Cell.register 0).addressCode := by
  have checked : row.ports.toList.all (fun port => nonzeroPort port.address) = true := by
    cases row with
    | mk family w => cases family <;> dsimp only [Row.ports] <;> decide
  have valid := List.all_eq_true.mp checked port (by simpa using member)
  cases address : port.address
  all_goals simp [address, nonzeroPort] at valid
  all_goals first
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair] at valid ⊢
      exact valid
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair]

end Airbender.Delegation.Proofs
