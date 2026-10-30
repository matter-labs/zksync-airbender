import Airbender.Import.SetupSourceBank
import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Airbender.Setup.SourceBank
open SourceProofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

private theorem contents_map {α β : Type} (bytes : β → List Char) (child : α → β)
    (entries : List α) :
    SourceData.contents bytes (entries.map child) =
      SourceData.contents (fun entry => bytes (child entry)) entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simpa only [List.map_cons, SourceData.contents] using
        congrArg (fun tail => bytes (child entry) ++ ',' :: tail) ih

private theorem object_contents_map {α β : Type} (keys bytes : β → List Char)
    (child : α → β) (entries : List α) :
    SourceData.objectContents keys bytes (entries.map child) =
      SourceData.objectContents (fun entry => keys (child entry))
        (fun entry => bytes (child entry)) entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simpa only [List.map_cons, SourceData.objectContents] using
        congrArg (fun tail => keys (child entry) ++ ':' :: (bytes (child entry) ++ ',' :: tail)) ih

theorem sharedArrayNode_eq {α : Type} (child : α → SourceData.Node) (entries : List α) :
    sharedArrayNode child entries = SourceData.arrayNode child entries := by
  simp only [sharedArrayNode, SourceData.arrayNode, SourceData.arrayBytes,
    contents_map, List.map_map, Function.comp_def]

theorem sharedObjectNode_eq {α : Type} (key : α → String) (child : α → SourceData.Node)
    (entries : List α) :
    sharedObjectNode key child entries = SourceData.objectNode key child entries := by
  simp only [sharedObjectNode, SourceData.objectNode, SourceData.objectBytes,
    object_contents_map, List.map_map, Function.comp_def]

/-- The table interpreter preserves exact source parsing at each depth.
Each scalar check has a proved parser specification. -/
theorem evaluate_source (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (stringChecked : ∀ index, check_string (strings index) = true)
    (numberChecked : ∀ index, check_number_token (tokens index) = true) (fuel index : Nat) :
    NodeSource (evaluate strings tokens bank fuel index) := by
  induction fuel generalizing index with
  | zero => exact null_node_source
  | succ fuel ih =>
    simp only [evaluate, sharedArrayNode_eq, sharedObjectNode_eq]
    cases bank.get index with
    | null => exact null_node_source
    | boolean value => exact boolean_node_source value
    | number index => exact number_node_source (tokens index) (numberChecked index)
    | string index => exact string_node_source (strings index) (stringChecked index)
    | array entries => exact array_node_source _ ih entries
    | object entries =>
      exact object_node_source (fun entry => strings entry.1)
        (fun entry => evaluate strings tokens bank fuel entry.2)
        (fun entry => stringChecked entry.1) (fun entry => ih entry.2) entries

theorem evaluate_object_eager (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (stringChecked : ∀ index, check_string (strings index) = true)
    (numberChecked : ∀ index, check_number_token (tokens index) = true)
    (fuel index : Nat) (entries : List (Nat × Nat)) (selected : bank.get index = .object entries) :
    EagerSource (evaluate strings tokens bank (fuel + 1) index).bytes
      (evaluate strings tokens bank (fuel + 1) index).value := by
  simp only [evaluate, selected, sharedObjectNode_eq]
  exact object_node_eager (fun entry => strings entry.1)
    (fun entry => evaluate strings tokens bank fuel entry.2)
    (fun entry => stringChecked entry.1)
    (fun entry => evaluate_source strings tokens bank stringChecked numberChecked fuel entry.2) entries

end Airbender.Setup.SourceBank
