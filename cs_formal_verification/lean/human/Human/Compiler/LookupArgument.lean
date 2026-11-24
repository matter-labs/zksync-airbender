module
public import Human.Import.Schema

@[expose] public section

namespace Airbender.Compiler

/-- The logical lookup-argument boundary, before challenge compression. The
requests are actual emitted tuples. The right side repeats independently
interpreted setup rows according to natural multiplicities. Exact tuple
matching is assumed; equality of sampled rational sums does not imply it. -/
structure LookupArgument {ι α : Type} (table : ι → α) (requests : List α) where
  /-- The setup row indices used by the argument. -/
  rows : List ι
  /-- The natural count of each selected setup row. -/
  multiplicity : ι → Nat
  /-- Every emitted tuple matches the selected setup multiset. -/
  balance : requests.Perm (rows.flatMap fun row => List.replicate (multiplicity row) (table row))

/-- One exact logical argument per lookup group. Native bindings instantiate
the table interpretation and enabled emitted tuples; they supply no sampled
sum-to-permutation implication or physical field-counter interpretation. -/
def GroupedLookupArguments {κ ι α : Type} (tables : κ → ι → α)
    (requests : κ → List α) : Type :=
  (group : κ) → LookupArgument (tables group) (requests group)

end Airbender.Compiler
