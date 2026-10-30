import Airbender.Import.SetupSourceData

namespace Airbender.Setup.SourceBank

/-- Source descriptions store every field and element in source order.
The interpreter uses a bounded depth. It adds no semantic assertion. -/
inductive Description where
  | null
  | boolean (value : Bool)
  | number (index : Nat)
  | string (index : Nat)
  | array (entries : List Nat)
  | object (entries : List (Nat × Nat))

inductive Bank where
  | leaf (description : Description)
  | branch (split : Nat) (left right : Bank)

def Bank.get : Bank → Nat → Description
  | .leaf value, _ => value
  | .branch split left right, index =>
    if index < split then left.get index else right.get index

/-- Evaluate each array child once. Both fields use the same retained node. -/
def sharedArrayNode {α : Type} (child : α → SourceData.Node) (entries : List α) : SourceData.Node :=
  let nodes := entries.map child
  ⟨SourceData.arrayBytes SourceData.Node.bytes nodes,
    .arr (nodes.map SourceData.Node.value).toArray⟩

/-- Evaluate each object child once. Keep each original key and its order. -/
def sharedObjectNode {α : Type} (key : α → String) (child : α → SourceData.Node)
    (entries : List α) : SourceData.Node :=
  let nodes := entries.map (fun entry => (key entry, child entry))
  ⟨SourceData.objectBytes (fun entry => SourceData.stringBytes entry.1)
      (fun entry => entry.2.bytes) nodes,
    Lean.Json.mkObj (nodes.map (fun entry => (entry.1, entry.2.value)))⟩

def evaluate (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank) :
    Nat → Nat → SourceData.Node
  | 0, _ => SourceData.nullNode
  | fuel + 1, index =>
    match bank.get index with
    | .null => SourceData.nullNode
    | .boolean value => SourceData.booleanNode value
    | .number index => SourceData.numberNode (tokens index)
    | .string index => SourceData.stringNode (strings index)
    | .array entries => sharedArrayNode (evaluate strings tokens bank fuel) entries
    | .object entries => sharedObjectNode (fun entry => strings entry.1)
        (fun entry => evaluate strings tokens bank fuel entry.2) entries

end Airbender.Setup.SourceBank
