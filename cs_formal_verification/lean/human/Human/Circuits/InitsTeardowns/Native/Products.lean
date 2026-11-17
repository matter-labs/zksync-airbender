module
public import Human.Circuits.InitsTeardowns.Native.Model

@[expose] public section

namespace Airbender.InitsTeardowns.Native
variable [CommRing E]

/-- The native memory bank of an initialization instance.
    Native memory column `column` holds the logical variable `column + offset` of the instance. -/
def memoryBank {layout : InitsTeardowns.Layout} (offset : Nat) (witness : InitsTeardowns.Witness p layout) : Raw p :=
  fun row column => witness.assignment row (column + offset)

/-- The native product over every row of a designated imported output wire.
    Noncomputable prevents large closed domains from being hoisted into native
    module initializers, even when these definitions occur only in proofs. -/
noncomputable def rootProduct (artifact : Artifact) (tree : Tree) (wires : Wires E) : E :=
  ((List.finRange artifact.layout.rows).map fun row => wires tree.output row.val).prod

end Airbender.InitsTeardowns.Native
