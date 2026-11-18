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

/-- Raw memory-bank columns by row: row position, then memory column, to field value. -/
abbrev Raw (p : Nat) := Nat → Nat → ZMod p

variable [CommRing E]

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

end Airbender.InitsTeardowns.Native
