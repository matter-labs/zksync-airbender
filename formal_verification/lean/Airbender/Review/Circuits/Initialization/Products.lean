import Airbender.Review.Circuits.Initialization.Model

namespace Airbender.Initialization
variable [CommRing E]

/-- Window-major native RAM tokens. This is a symbolic mathematical list;
    native compilation must never materialize the full 2^24/2^23-row domain. -/
noncomputable def ramTokens (layout : Layout) (parameters : Parameters p E)
    (raw : Raw p) (phase : Phase) : List (Trace.MemoryToken p) :=
  (layout.leaves phase).flatMap fun leaf =>
    (List.finRange layout.rows).map fun row => leaf.token layout parameters raw row.val

/-- The native product over every row of a designated imported output wire.
    Noncomputable prevents large closed domains from being hoisted into native
    module initializers, even when these definitions occur only in proofs. -/
noncomputable def rootProduct (artifact : Artifact) (tree : Tree) (wires : Wires E) : E :=
  ((List.finRange artifact.layout.rows).map fun row => wires tree.output row.val).prod

end Airbender.Initialization
