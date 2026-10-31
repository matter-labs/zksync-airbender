import Airbender.Import.SetupSourceBank
import Lean
open Airbender.Setup Airbender.Setup.SourceData Airbender.Setup.SourceBank
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
namespace Airbender.Setup.SourceCharacters.Renderer

def contentsWith {α : Type} (render : α → List Char → List Char) :
    List α → List Char → List Char
  | [], tail => tail
  | [entry], tail => render entry tail
  | entry :: next :: rest, tail => render entry (',' :: contentsWith render (next :: rest) tail)

theorem contentsWith_sound {α : Type} (render : α → List Char → List Char)
    (bytes : α → List Char) (sound : ∀ entry tail, render entry tail = bytes entry ++ tail)
    (entries : List α) (tail : List Char) :
    contentsWith render entries tail = contents bytes entries ++ tail := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    cases rest with
    | nil => exact sound head tail
    | cons next rest =>
      simp only [contentsWith, contents, sound, ih, List.append_assoc, List.cons_append]

theorem contents_map {α β : Type} (bytes : β → List Char) (f : α → β) (entries : List α) :
    contents bytes (entries.map f) = contents (fun a => bytes (f a)) entries := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest => simpa only [List.map_cons, contents] using congrArg (fun tail => bytes (f head) ++ ',' :: tail) ih

def objectWith {α : Type} (key : α → List Char) (render : α → List Char → List Char) :
    List α → List Char → List Char
  | [], tail => tail
  | [entry], tail => key entry ++ ':' :: render entry tail
  | entry :: next :: rest, tail =>
    key entry ++ ':' :: render entry (',' :: objectWith key render (next :: rest) tail)

theorem objectWith_sound {α : Type} (key : α → List Char)
    (render : α → List Char → List Char) (bytes : α → List Char)
    (sound : ∀ entry tail, render entry tail = bytes entry ++ tail)
    (entries : List α) (tail : List Char) :
    objectWith key render entries tail = objectContents key bytes entries ++ tail := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    cases rest with
    | nil => simp only [objectWith, objectContents, sound, List.append_assoc, List.cons_append]
    | cons next rest =>
      simp only [objectWith, objectContents, sound, ih, List.append_assoc, List.cons_append]

theorem objectContents_map {α β : Type} (keys bytes : β → List Char) (f : α → β) (entries : List α) :
    objectContents keys bytes (entries.map f) =
      objectContents (fun a => keys (f a)) (fun a => bytes (f a)) entries := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simpa only [List.map_cons, objectContents] using
        congrArg (fun tail => keys (f head) ++ ':' :: (bytes (f head) ++ ',' :: tail)) ih

def render (strings : Nat → String) (tokens : Nat → NumberToken) (bank : Bank) :
    Nat → Nat → List Char → List Char
  | 0, _, tail => nullBytes ++ tail
  | fuel + 1, index, tail =>
    match bank.get index with
    | .null => nullBytes ++ tail
    | .boolean value => booleanBytes value ++ tail
    | .number i => (tokens i).bytes ++ tail
    | .string i => stringBytes (strings i) ++ tail
    | .array entries => '[' :: contentsWith (render strings tokens bank fuel) entries (']' :: tail)
    | .indexedArray children entries => '[' :: contentsWith (fun i => render strings tokens bank fuel (children i)) entries (']' :: tail)
    | .object entries => '{' :: objectWith (fun entry => stringBytes (strings entry.1))
        (fun entry => render strings tokens bank fuel entry.2) entries ('}' :: tail)

theorem render_sound (strings : Nat → String) (tokens : Nat → NumberToken) (bank : Bank)
    (fuel index : Nat) (tail : List Char) :
    render strings tokens bank fuel index tail = (evaluate strings tokens bank fuel index).bytes ++ tail := by
  induction fuel generalizing index tail with
  | zero => rfl
  | succ fuel ih =>
    cases h : bank.get index <;> simp only [render, evaluate, h] <;> try rfl
    case array entries =>
      rw [contentsWith_sound _ _ (fun i t => ih i t)]
      simp only [sharedArrayNode, arrayBytes, contents_map, List.cons_append, List.append_assoc, List.nil_append]
    case indexedArray children entries =>
      rw [contentsWith_sound _ _ (fun i t => ih (children i) t)]
      simp only [sharedArrayNode, arrayBytes, contents_map, List.cons_append, List.append_assoc, List.nil_append]
    case object entries =>
      rw [objectWith_sound _ _ _ (fun i t => ih i.2 t)]
      simp only [sharedObjectNode, objectBytes, objectContents_map, List.cons_append, List.append_assoc, List.nil_append]
theorem render_bytes (strings : Nat → String) (tokens : Nat → NumberToken) (bank : Bank)
    (fuel index : Nat) :
    (evaluate strings tokens bank fuel index).bytes = render strings tokens bank fuel index [] := by
  simpa only [List.append_nil] using (render_sound strings tokens bank fuel index []).symm

end Airbender.Setup.SourceCharacters.Renderer
