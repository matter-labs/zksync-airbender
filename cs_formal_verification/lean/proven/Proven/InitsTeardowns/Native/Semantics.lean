module
public import Human.Circuits.InitsTeardowns.Native.Products

@[expose] public section

/-! The tree form of the initialization products, a proof step. `Bridge.lean` derives `Accepted` from the compiled
    acceptance `NativeMemory.InitializationHolds` of the bound circuit. -/

namespace Airbender.InitsTeardowns.Native

/-- Extension wires of the extracted graph by row. -/
abbrev Wires (E : Type) := Port → Nat → E

variable [CommRing E]

/-- The low address limb of a four-byte word row. -/
def addressLo (row : Nat) : Nat := (4 * row) % 65536

/-- The high address limb of a four-byte word row in the public window of `set`. -/
def addressHi (layout : Layout) (parameters : Parameters p E) (set row : Nat) : Nat :=
  row / 16384 + parameters.windows set * layout.stride

/-- The timestamp limbs of a leaf: zero for an initialization. -/
def Leaf.time (leaf : Leaf) (raw : Raw p) (row : Nat) : ZMod p × ZMod p :=
  match leaf.phase with
  | .initial => (0, 0)
  | .terminal => (raw row leaf.columns.timeLo, raw row leaf.columns.timeHi)

/-- The value limbs of a leaf: zero for an initialization. -/
def Leaf.value (leaf : Leaf) (raw : Raw p) (row : Nat) : ZMod p × ZMod p :=
  match leaf.phase with
  | .initial => (0, 0)
  | .terminal => (raw row leaf.columns.valueLo, raw row leaf.columns.valueHi)

/-- The factor of one leaf. `Bridge.lean` proves it equal to `NativeMemory.initializationTuple`. -/
def Leaf.factor (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) (leaf : Leaf) : E :=
  parameters.additive + 1 +
    parameters.weights 0 * parameters.embed (addressLo row : ZMod p) +
    parameters.weights 1 * parameters.embed (addressHi layout parameters leaf.set row : ZMod p) +
    parameters.weights 2 * parameters.embed (leaf.time raw row).1 +
    parameters.weights 3 * parameters.embed (leaf.time raw row).2 +
    parameters.weights 4 * parameters.embed (leaf.value raw row).1 +
    parameters.weights 5 * parameters.embed (leaf.value raw row).2

/-- One extracted gate holds on one row. -/
def Gate.Sat (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (row : Nat) : Gate → Prop
  | .pair output left right => wires output row =
      left.factor layout parameters raw row * right.factor layout parameters raw row
  | .product output left right => wires output row = wires left row * wires right row
  | .copy output input => wires output row = wires input row

/-- The value of a tree on one row. -/
def Tree.eval (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) : Tree → E
  | .pair _ left right =>
      left.factor layout parameters raw row * right.factor layout parameters raw row
  | .product _ left right => left.eval layout parameters raw row * right.eval layout parameters raw row
  | .copy _ input => input.eval layout parameters raw row

/-- Every extracted gate holds on every native row. -/
def Accepted (artifact : Artifact) (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) : Prop :=
  ∀ row : Fin artifact.layout.rows, ∀ gate ∈ artifact.gates.toList,
    gate.Sat artifact.layout parameters raw wires row.val

end Airbender.InitsTeardowns.Native
