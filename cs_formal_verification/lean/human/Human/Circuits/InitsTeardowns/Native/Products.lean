module
public import Human.Circuits.InitsTeardowns.Native.Extract

@[expose] public section

namespace Airbender.InitsTeardowns.Native
variable [CommRing E]

/-- The native memory bank of an initialization instance.
    Native memory column `column` holds the logical variable `column + offset` of the instance. -/
def memoryBank {layout : InitsTeardowns.Layout} (offset : Nat) (witness : InitsTeardowns.Witness p layout) : Raw p :=
  fun row column => witness.assignment row (column + offset)

/-- The physical wires of row `row` with the virtual setup address limbs that the verifier computes for the row
    (`InitsTeardowns.setupLow`, `InitsTeardowns.setupHigh`). Every other wire is `physical`. -/
def withSetupAddresses (layout : InitsTeardowns.Layout) (row : Nat) (physical : GKRAddress → ZMod p) :
    GKRAddress → ZMod p
  | .VirtualSetup .InitsAndTeardownsLow => (InitsTeardowns.setupLow layout row : ZMod p)
  | .VirtualSetup .InitsAndTeardownsHigh => (InitsTeardowns.setupHigh layout row : ZMod p)
  | address => physical address

/-- The product over every native row of the output wire of an extracted tree.
    Noncomputable prevents large closed domains from being hoisted into native
    module initializers, even when these definitions occur only in proofs. -/
noncomputable def outputProduct (artifact : Artifact) (tree : Tree) (values : Nat → GKRAddress → E) : E :=
  ((List.finRange artifact.layout.rows).map fun row => values row.val (Extract.address tree.output)).prod

end Airbender.InitsTeardowns.Native
