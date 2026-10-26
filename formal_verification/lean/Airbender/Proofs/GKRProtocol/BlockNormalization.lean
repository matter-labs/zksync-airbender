import Airbender.Proofs.GKRProtocol.ColumnSlices
import Mathlib.Tactic.Ring

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

def mergeSetupBlocks : Setup.Block → Setup.Block → Option Setup.Block
  | .affine left first step, .affine right next other =>
      if step = other ∧ (first : Int) + step * left = next then
        some (.affine (left + right) first step)
      else none
  | .periodic left step values, .periodic right other next =>
      if step = 0 ∧ other = 0 ∧ values = next then
        some (.periodic (left + right) 0 values)
      else none
  | _, _ => none

theorem affine_blocks_merge (left right first next : Nat) (step : Int)
    (start : (first : Int) + step * left = next) (tail : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (.affine (left + right) first step :: tail) index =
      Setup.getFromBlocks (.affine left first step :: .affine right next step :: tail) index := by
  by_cases leading : index < left
  · have whole : index < left + right := by omega
    simp only [Setup.getFromBlocks, Setup.Block.length, if_pos leading, if_pos whole,
      Setup.Block.get?]
  · by_cases trailing : index - left < right
    · have whole : index < left + right := by omega
      have splitIndex : (index : Int) = (left : Int) + (index - left : Nat) := by
        exact_mod_cast (show index = left + (index - left) by omega)
      have formula : (first : Int) + step * index = (next : Int) + step * (index - left : Nat) := by
        rw [splitIndex, ← start]
        ring
      simp only [Setup.getFromBlocks, Setup.Block.length, if_pos whole, if_neg leading,
        if_pos trailing, Setup.Block.get?, formula]
    · have whole : ¬index < left + right := by omega
      simp only [Setup.getFromBlocks, Setup.Block.length, if_neg whole, if_neg leading,
        if_neg trailing]
      have position : index - (left + right) = index - left - right := by omega
      rw [position]

theorem periodic_zero_get (repetitions : Nat) (values : Array Nat) (index : Nat)
    (bounded : index < repetitions * values.size) :
    (Setup.Block.periodic repetitions 0 values).get? index =
      some ((values[index % values.size]?).getD 0) := by
  simp [Setup.Block.get?, Setup.Block.length, bounded]

theorem periodic_blocks_merge (left right : Nat) (values : Array Nat)
    (tail : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (.periodic (left + right) 0 values :: tail) index =
      Setup.getFromBlocks (.periodic left 0 values :: .periodic right 0 values :: tail) index := by
  by_cases leading : index < left * values.size
  · have whole : index < (left + right) * values.size := by rw [Nat.add_mul]; omega
    simp only [Setup.getFromBlocks, Setup.Block.length, if_pos leading, if_pos whole,
      periodic_zero_get _ _ _ leading, periodic_zero_get _ _ _ whole]
  · by_cases trailing : index - left * values.size < right * values.size
    · have whole : index < (left + right) * values.size := by rw [Nat.add_mul]; omega
      simp only [Setup.getFromBlocks, Setup.Block.length, if_pos whole, if_neg leading,
        if_pos trailing, periodic_zero_get _ _ _ whole, periodic_zero_get _ _ _ trailing]
      have splitIndex : index = (index - left * values.size) + left * values.size := by omega
      have residue : index % values.size = (index - left * values.size) % values.size := by
        calc
          _ = ((index - left * values.size) + left * values.size) % values.size :=
            congrArg (· % values.size) splitIndex
          _ = _ := by simp [Nat.add_mod]
      rw [residue]
    · have whole : ¬index < (left + right) * values.size := by rw [Nat.add_mul]; omega
      simp only [Setup.getFromBlocks, Setup.Block.length, if_neg whole, if_neg leading,
        if_neg trailing]
      have position : index - ((left + right) * values.size) =
          index - left * values.size - right * values.size := by rw [Nat.add_mul]; omega
      rw [position]

theorem mergeSetupBlocks_sound (left right joined : Setup.Block)
    (checked : mergeSetupBlocks left right = some joined) (tail : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (joined :: tail) index = Setup.getFromBlocks (left :: right :: tail) index := by
  cases left <;> cases right <;> simp only [mergeSetupBlocks] at checked
  all_goals try contradiction
  case affine.affine left first step right next other =>
    split_ifs at checked with guard
    · rcases guard with ⟨rfl, start⟩
      cases checked
      exact affine_blocks_merge left right first next step start tail index
  case periodic.periodic left step values right other next =>
    split_ifs at checked with guard
    · rcases guard with ⟨rfl, rfl, rfl⟩
      cases checked
      exact periodic_blocks_merge left right values tail index

def prependNormalizedBlock (block : Setup.Block) : List Setup.Block → List Setup.Block
  | [] => [block]
  | next :: rest =>
      match mergeSetupBlocks block next with
      | none => block :: next :: rest
      | some joined => joined :: rest

def normalizeSetupBlocks : List Setup.Block → List Setup.Block
  | [] => []
  | block :: rest => prependNormalizedBlock block (normalizeSetupBlocks rest)

theorem prependNormalizedBlock_value (block : Setup.Block) (tail : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (prependNormalizedBlock block tail) index =
      Setup.getFromBlocks (block :: tail) index := by
  cases tail with
  | nil => rfl
  | cons next rest =>
    cases found : mergeSetupBlocks block next with
    | none => simp only [prependNormalizedBlock, found]
    | some joined =>
      simp only [prependNormalizedBlock, found]
      exact mergeSetupBlocks_sound block next joined found rest index

theorem normalizeSetupBlocks_sound (blocks : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (normalizeSetupBlocks blocks) index = Setup.getFromBlocks blocks index := by
  induction blocks generalizing index with
  | nil => rfl
  | cons block rest ih =>
    rw [normalizeSetupBlocks, prependNormalizedBlock_value]
    simp only [Setup.getFromBlocks]
    split
    · rfl
    · exact ih _

theorem normalized_columns_agree (left right : Setup.Column)
    (checked : normalizeSetupBlocks left.blocks.toList = normalizeSetupBlocks right.blocks.toList)
    (index : Nat) : left.get? index = right.get? index := by
  change Setup.getFromBlocks left.blocks.toList index = Setup.getFromBlocks right.blocks.toList index
  rw [← normalizeSetupBlocks_sound left.blocks.toList index, checked, normalizeSetupBlocks_sound]

theorem mergeSetupBlocks_length (left right joined : Setup.Block)
    (checked : mergeSetupBlocks left right = some joined) :
    joined.length = left.length + right.length := by
  cases left <;> cases right <;> simp only [mergeSetupBlocks] at checked
  all_goals try contradiction
  case affine.affine =>
    split_ifs at checked
    cases checked
    rfl
  case periodic.periodic =>
    split_ifs at checked with guard
    rcases guard with ⟨rfl, rfl, rfl⟩
    cases checked
    simp only [Setup.Block.length, Nat.add_mul]

theorem prependNormalizedBlock_length (block : Setup.Block) (tail : List Setup.Block) :
    ((prependNormalizedBlock block tail).map Setup.Block.length).sum =
      block.length + (tail.map Setup.Block.length).sum := by
  cases tail with
  | nil => simp only [prependNormalizedBlock, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | cons next rest =>
    cases found : mergeSetupBlocks block next with
    | none => simp only [prependNormalizedBlock, found, List.map_cons, List.sum_cons]
    | some joined =>
      simp only [prependNormalizedBlock, found, List.map_cons, List.sum_cons]
      rw [mergeSetupBlocks_length block next joined found, Nat.add_assoc]

theorem normalizeSetupBlocks_length (blocks : List Setup.Block) :
    ((normalizeSetupBlocks blocks).map Setup.Block.length).sum = (blocks.map Setup.Block.length).sum := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    rw [normalizeSetupBlocks, prependNormalizedBlock_length, ih]
    rfl

theorem getFromBlocks_append (front back : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (front ++ back) index =
      if index < (front.map Setup.Block.length).sum then Setup.getFromBlocks front index
      else Setup.getFromBlocks back (index - (front.map Setup.Block.length).sum) := by
  induction front generalizing index with
  | nil => simp only [List.nil_append, List.map_nil, List.sum_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  | cons block rest ih =>
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    by_cases leading : index < block.length
    · have whole : index < block.length + (rest.map Setup.Block.length).sum := by omega
      simp only [Setup.getFromBlocks, if_pos leading, if_pos whole]
    · simp only [Setup.getFromBlocks, if_neg leading]
      rw [ih]
      by_cases middle : index - block.length < (rest.map Setup.Block.length).sum
      · have whole : index < block.length + (rest.map Setup.Block.length).sum := by omega
        simp only [if_pos middle, if_pos whole]
      · have whole : ¬index < block.length + (rest.map Setup.Block.length).sum := by omega
        simp only [if_neg middle, if_neg whole]
        have position : index - block.length - (rest.map Setup.Block.length).sum =
            index - (block.length + (rest.map Setup.Block.length).sum) := by omega
        rw [position]

theorem normalized_chunks_agree (left right : List (List Setup.Block))
    (checked : List.Forall₂ (fun first second => normalizeSetupBlocks first = normalizeSetupBlocks second) left right)
    (index : Nat) : Setup.getFromBlocks left.flatten index = Setup.getFromBlocks right.flatten index := by
  induction checked generalizing index with
  | nil => rfl
  | @cons first second left right same rest ih =>
    simp only [List.flatten_cons]
    rw [getFromBlocks_append first left.flatten index, getFromBlocks_append second right.flatten index]
    have lengths : (first.map Setup.Block.length).sum = (second.map Setup.Block.length).sum := by
      rw [← normalizeSetupBlocks_length first, same, normalizeSetupBlocks_length]
    rw [lengths]
    split
    · rw [← normalizeSetupBlocks_sound first index, same, normalizeSetupBlocks_sound]
    · exact ih _

end Airbender.Compiler
