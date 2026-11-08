module
public import Slop.Blake2G.CallControl
public import Slop.Delegation.IndexedPaths

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem control_edges {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .blakeG) :
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) =
      data.rows.map (fun row => (readToken row.assignment importedConstraintsMemoryPorts[8],
        row.writeToken importedConstraintsMemoryPorts[8])) := by
  simp only [Delegation.MemoryData.steps, List.filter_flatMap, List.map_eq_flatMap]
  change (data.rows.map _).flatten = (data.rows.map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ member
    change kind = .blakeG at same
    subst kind
    simp [Delegation.Row.memorySteps, Delegation.Row.ports, importedConstraintsMemoryPorts,
      readToken, MemoryAddress.code, Cell.addressCode, pairCode, Nat.pair_eq_pair]

end Airbender.Blake2G.Proofs
