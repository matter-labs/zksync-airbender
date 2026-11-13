module
public import Human.Circuits.InitsTeardowns.Model
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

namespace Airbender.InitsTeardowns.Native

/-- An extension-field wire in the imported no-cache GKR graph. -/
structure Port where
  /-- The native layer index. -/
  layer : Nat
  /-- The extension wire index in that layer. -/
  offset : Nat
  deriving Repr, DecidableEq

/-- Actual scalar teardown columns, in timestamp/value order. -/
structure Columns where
  /-- The low timestamp memory column. -/
  timeLo : Nat
  /-- The high timestamp memory column. -/
  timeHi : Nat
  /-- The low value memory column. -/
  valueLo : Nat
  /-- The high value memory column. -/
  valueHi : Nat
  deriving Repr, DecidableEq

inductive Phase where
  | initial | terminal
  deriving Repr, DecidableEq

structure Leaf where
  /-- The initialization or teardown side. -/
  phase : Phase
  /-- The native initialization set index. -/
  set : Nat
  /-- The native teardown columns in set order. -/
  columns : Columns
  deriving Repr, DecidableEq

/-- Only the three relations used by the native RAM boundary slices. -/
inductive Gate where
  | pair (output : Port) (left right : Leaf)
  | product (output left right : Port)
  | copy (output input : Port)
  deriving Repr, DecidableEq

def Gate.output : Gate → Port
  | .pair output _ _ | .product output _ _ | .copy output _ => output

/-- A dependency tree emitted from the actual producer graph, not supplied by
    the caller. Its connection to every selected native gate is checked below. -/
inductive Tree where
  | pair (output : Port) (left right : Leaf)
  | product (output : Port) (left right : Tree)
  | copy (output : Port) (input : Tree)
  deriving Repr, DecidableEq

def Tree.output : Tree → Port
  | .pair output _ _ | .product output _ _ | .copy output _ => output

def Tree.leaves : Tree → List Leaf
  | .pair _ left right => [left, right]
  | .product _ left right => left.leaves ++ right.leaves
  | .copy _ input => input.leaves

/-- Exact gate membership and child/output wiring, including the final gates
    stored under `gates_with_external_connections` in the native artifacts. -/
inductive Tree.Follows (gates : Array Gate) : Tree → Prop where
  | pair {out : Port} {left right : Leaf}
      (member : Gate.pair out left right ∈ gates.toList) :
      Follows gates (.pair out left right)
  | product {out : Port} {left right : Tree}
      (member : Gate.product out left.output right.output ∈ gates.toList)
      (lhs : Follows gates left) (rhs : Follows gates right) :
      Follows gates (.product out left right)
  | copy {out : Port} {input : Tree} (member : Gate.copy out input.output ∈ gates.toList)
      (source : Follows gates input) : Follows gates (.copy out input)

/-- All numeric geometry and scalar columns come from the imported layout.
    `stride` is the high-limb window increment derived from trace length and
    word bits. The checked native artifacts use four-byte words. -/
structure Layout where
  /-- The number of native rows. -/
  rows : Nat
  /-- The byte-address shift for one word. -/
  wordBits : Nat
  /-- The shift of the public window index in the high address limb. -/
  highOffset : Nat
  /-- The high-limb increment for adjacent windows. -/
  stride : Nat
  /-- The number of windows in the 32-bit address space. -/
  slots : Nat
  /-- The native memory-bank width. -/
  memoryWidth : Nat
  /-- The native teardown columns in set order. -/
  columns : Array Columns
  deriving Repr, DecidableEq

/-- Only the small native set domain is enumerated here (eight or two sets). -/
def Layout.leaves (layout : Layout) (phase : Phase) : List Leaf :=
  (List.finRange layout.columns.size).map fun set => ⟨phase, set.val, layout.columns[set]⟩

structure Artifact where
  /-- The geometry and columns extracted from the artifact. -/
  layout : Layout
  /-- The native relations in the two output dependency trees. -/
  gates : Array Gate
  /-- The teardown output dependency tree. -/
  terminal : Tree
  /-- The initialization output dependency tree. -/
  initial : Tree

/-- Public window choices and the six native linearization challenges. The RAM
    address-space contribution is the unweighted constant one. -/
structure Parameters (p : Nat) (E : Type) [CommRing E] where
  /-- The base-field embedding into the extension ring. -/
  embed : ZMod p →+* E
  /-- The additive memory-product challenge. -/
  additive : E
  /-- The six address, timestamp and value challenges. -/
  weights : Fin 6 → E
  /-- The public top-bits value for each set. -/
  windows : Nat → Nat

abbrev Raw (p : Nat) := Nat → Nat → ZMod p
abbrev Wires (E : Type) := Port → Nat → E

variable [CommRing E]

def addressLo (row : Nat) : Nat := (4 * row) % 65536

def addressHi (layout : Layout) (parameters : Parameters p E) (set row : Nat) : Nat :=
  row / 16384 + parameters.windows set * layout.stride

def Leaf.time (leaf : Leaf) (raw : Raw p) (row : Nat) : ZMod p × ZMod p :=
  match leaf.phase with
  | .initial => (0, 0)
  | .terminal => (raw row leaf.columns.timeLo, raw row leaf.columns.timeHi)

def Leaf.value (leaf : Leaf) (raw : Raw p) (row : Nat) : ZMod p × ZMod p :=
  match leaf.phase with
  | .initial => (0, 0)
  | .terminal => (raw row leaf.columns.valueLo, raw row leaf.columns.valueHi)

/-- Boundary tokens are computed from native addresses and actual raw columns.
    Value and timestamp limbs are deliberately not restricted to 16 bits. -/
def Leaf.token (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) (leaf : Leaf) : Trace.MemoryToken p :=
  ⟨Nat.pair 1 (Nat.pair (addressLo row) (addressHi layout parameters leaf.set row)),
    leaf.time raw row, Nat.pair (leaf.value raw row).1.val (leaf.value raw row).2.val⟩

/-- The native six-weight encoding of the existing memory-history token type.
    No sampled-product equality is interpreted as logical token matching. -/
def Parameters.encode (parameters : Parameters p E) (token : Trace.MemoryToken p) : E :=
  let address := Nat.unpair token.address
  let limbs := Nat.unpair address.2
  let value := Nat.unpair token.value
  parameters.additive + parameters.embed (address.1 : ZMod p) +
    parameters.weights 0 * parameters.embed (limbs.1 : ZMod p) +
    parameters.weights 1 * parameters.embed (limbs.2 : ZMod p) +
    parameters.weights 2 * parameters.embed token.time.1 +
    parameters.weights 3 * parameters.embed token.time.2 +
    parameters.weights 4 * parameters.embed (value.1 : ZMod p) +
    parameters.weights 5 * parameters.embed (value.2 : ZMod p)

/-- `evaluate_init` / `evaluate_teardown`: address space, address, timestamp,
    then value. No range condition is imposed on raw time/value limbs. -/
def Leaf.factor (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) (leaf : Leaf) : E :=
  parameters.additive + 1 +
    parameters.weights 0 * parameters.embed (addressLo row : ZMod p) +
    parameters.weights 1 * parameters.embed (addressHi layout parameters leaf.set row : ZMod p) +
    parameters.weights 2 * parameters.embed (leaf.time raw row).1 +
    parameters.weights 3 * parameters.embed (leaf.time raw row).2 +
    parameters.weights 4 * parameters.embed (leaf.value raw row).1 +
    parameters.weights 5 * parameters.embed (leaf.value raw row).2

def Gate.Sat (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (row : Nat) : Gate → Prop
  | .pair output left right => wires output row =
      left.factor layout parameters raw row * right.factor layout parameters raw row
  | .product output left right => wires output row = wires left row * wires right row
  | .copy output input => wires output row = wires input row

def Tree.eval (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) : Tree → E
  | .pair _ left right =>
      left.factor layout parameters raw row * right.factor layout parameters raw row
  | .product _ left right => left.eval layout parameters raw row * right.eval layout parameters raw row
  | .copy _ input => input.eval layout parameters raw row

/-- Actual imported GKR acceptance on every native row. Ordinary empty equation
    arrays do not establish this predicate. Logical matching remains separate. -/
def Accepted (artifact : Artifact) (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) : Prop :=
  ∀ row : Fin artifact.layout.rows, ∀ gate ∈ artifact.gates.toList,
    gate.Sat artifact.layout parameters raw wires row.val

end Airbender.InitsTeardowns.Native
