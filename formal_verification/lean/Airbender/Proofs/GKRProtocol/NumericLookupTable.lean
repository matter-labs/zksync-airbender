import Mathlib.Data.List.TakeDrop

namespace Airbender.Compiler.NumericPolynomialChecks
set_option warningAsError true

/-- Store branch sizes so each lookup uses one numerical comparison per node. -/
inductive LookupTable (α : Type) where
  | leaf (items : List α)
  | branch (leftSize : Nat) (left right : LookupTable α)

def LookupTable.size : LookupTable α → Nat
  | .leaf items => items.length
  | .branch leftSize _ right => leftSize + right.size

def LookupTable.toList : LookupTable α → List α
  | .leaf items => items
  | .branch _ left right => left.toList ++ right.toList

def LookupTable.valid : LookupTable α → Bool
  | .leaf _ => true
  | .branch leftSize left right => leftSize == left.size && left.valid && right.valid

def LookupTable.getD (table : LookupTable α) (index : Nat) (fallback : α) : α :=
  match table with
  | .leaf items => (items[index]?).getD fallback
  | .branch leftSize left right =>
      if index < leftSize then left.getD index fallback
      else right.getD (index - leftSize) fallback
termination_by structural table

def LookupTable.ofList (depth : Nat) (items : List α) : LookupTable α :=
  match depth with
  | 0 => .leaf items
  | depth + 1 =>
      if items.length ≤ 16 then .leaf items
      else .branch (items.length / 2) (ofList depth (items.take (items.length / 2)))
        (ofList depth (items.drop (items.length / 2)))
termination_by structural depth

theorem LookupTable.toList_ofList (depth : Nat) (items : List α) :
    (ofList depth items).toList = items := by
  induction depth generalizing items with
  | zero => rfl
  | succ depth ih =>
      simp only [ofList]
      split
      · rfl
      · simp only [toList, ih, List.take_append_drop]

theorem LookupTable.size_ofList (depth : Nat) (items : List α) :
    (ofList depth items).size = items.length := by
  induction depth generalizing items with
  | zero => rfl
  | succ depth ih =>
      simp only [ofList]
      split
      · rfl
      · simp only [size, ih, List.length_drop]
        omega

theorem LookupTable.valid_ofList (depth : Nat) (items : List α) :
    (ofList depth items).valid = true := by
  induction depth generalizing items with
  | zero => rfl
  | succ depth ih =>
      simp only [ofList]
      split
      · rfl
      · simp only [valid, size_ofList, List.length_take, ih, Bool.and_true, beq_iff_eq]
        omega

theorem LookupTable.size_eq_length (table : LookupTable α) (checked : table.valid = true) :
    table.size = table.toList.length := by
  induction table with
  | leaf _ => rfl
  | branch leftSize left right first second =>
      simp only [valid, Bool.and_eq_true, beq_iff_eq] at checked
      simp only [size, toList, List.length_append, checked.1.1,
        first checked.1.2, second checked.2]

theorem LookupTable.getD_eq (table : LookupTable α) (checked : table.valid = true)
    (index : Nat) (fallback : α) :
    table.getD index fallback = (table.toList[index]?).getD fallback := by
  induction table generalizing index with
  | leaf _ => rfl
  | branch leftSize left right first second =>
      simp only [valid, Bool.and_eq_true, beq_iff_eq] at checked
      have leftSizeEq := left.size_eq_length checked.1.2
      simp only [getD, toList, checked.1.1, leftSizeEq, List.getElem?_append]
      by_cases inside : index < left.toList.length
      · simpa only [if_pos inside] using first checked.1.2 index
      · simpa only [if_neg inside] using second checked.2 (index - left.toList.length)

end Airbender.Compiler.NumericPolynomialChecks
