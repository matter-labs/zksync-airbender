import Airbender.Import.Schema

namespace Airbender.Compiler

/-- The logical lookup-argument boundary, before challenge compression. The
requests are actual emitted tuples. The right side repeats independently
interpreted setup rows according to natural multiplicities. Exact tuple
matching is assumed; equality of sampled rational sums does not imply it. -/
structure LookupArgument {ι α : Type} (table : ι → α) (requests : List α) where
  rows : List ι
  multiplicity : ι → Nat
  balance : requests.Perm (rows.flatMap fun row => List.replicate (multiplicity row) (table row))

end Airbender.Compiler
