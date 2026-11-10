import Mathlib.Data.List.Sort

namespace Airbender.Compiler.WiringChecks.KeySort
set_option warningAsError true

def merge : Nat → List Nat → List Nat → List Nat
  | 0, left, right => left ++ right
  | _ + 1, [], right => right
  | _ + 1, left, [] => left
  | fuel + 1, first :: left, second :: right =>
      if first ≤ second then first :: merge fuel left (second :: right)
      else second :: merge fuel (first :: left) right

theorem move_head (key : Nat) (left right : List Nat) :
    (key :: (left ++ right)).Perm (left ++ key :: right) := by
  induction left with
  | nil => rfl
  | cons first rest ih => exact (List.Perm.swap _ _ _).trans (List.Perm.cons first ih)

theorem merge_perm (fuel : Nat) (left right : List Nat) :
    (merge fuel left right).Perm (left ++ right) := by
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih =>
      cases left with
      | nil => simp [merge]
      | cons first left =>
          cases right with
          | nil => simp [merge]
          | cons second right =>
              simp only [merge]
              split
              · exact List.Perm.cons first (ih left (second :: right))
              · exact (List.Perm.cons second (ih (first :: left) right)).trans (move_head second (first :: left) right)

def pairs : List (List Nat) → List (List Nat)
  | first :: second :: rest => merge (first.length + second.length) first second :: pairs rest
  | rest => rest

theorem pairs_perm (chunks : List (List Nat)) : (pairs chunks).flatten.Perm chunks.flatten := by
  cases chunks with
  | nil => rfl
  | cons first tail =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          simp only [pairs, List.flatten_cons]
          simpa only [List.append_assoc] using (merge_perm _ first second).append (pairs_perm rest)
termination_by chunks.length

def passes : Nat → List (List Nat) → List Nat
  | 0, chunks => chunks.flatten
  | _ + 1, [] => []
  | _ + 1, [chunk] => chunk
  | fuel + 1, chunks => passes fuel (pairs chunks)

theorem passes_perm (fuel : Nat) (chunks : List (List Nat)) :
    (passes fuel chunks).Perm chunks.flatten := by
  induction fuel generalizing chunks with
  | zero => rfl
  | succ fuel ih =>
      cases chunks with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => simp [passes]
          | cons second rest => exact (ih (pairs (first :: second :: rest))).trans (pairs_perm _)

def sort (items : List Nat) : List Nat := passes items.length (items.map fun item => [item])

theorem sort_perm (items : List Nat) : (sort items).Perm items := by
  have flatten : (items.map fun item => [item]).flatten = items := by
    induction items with
    | nil => rfl
    | cons first rest ih =>
        change first :: (rest.map fun item => [item]).flatten = first :: rest
        exact congrArg (List.cons first) ih
  simpa only [sort, flatten] using passes_perm items.length (items.map fun item => [item])

end Airbender.Compiler.WiringChecks.KeySort
