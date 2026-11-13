module
public import Human.Helpers.Delegation.Memory
public import Proven.KernelRfl
public import Proven.OpIndex
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.Keccak.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem pointer_copies {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .keccak) :
    ∀ edge ∈ data.steps, edge.1.address = (Cell.register 11).addressCode → edge.1.word = edge.2.word := by
  intro edge member address
  obtain ⟨row, rowMember, edgeMember⟩ := List.mem_flatMap.mp member
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ rowMember
    change kind = .keccak at same
    subst kind
    simp [Delegation.Row.ports, importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | simp [readToken, MemoryAddress.code, Cell.addressCode] at address

end Airbender.Keccak.Proofs
