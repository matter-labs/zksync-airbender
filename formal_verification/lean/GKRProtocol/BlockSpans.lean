import GKRProtocol.BlockNormalization

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

theorem affine_block_span (leftLength rightLength first next offset index : Nat) (step : Int)
    (leftBound : offset + index < leftLength) (rightBound : index < rightLength)
    (same : (first : Int) + step * offset = next) :
    (Setup.Block.affine leftLength first step).get? (offset + index) =
      (Setup.Block.affine rightLength next step).get? index := by
  have formula : (first : Int) + step * (offset + index : Nat) = (next : Int) + step * index := by
    rw [Nat.cast_add, ← same]
    ring
  simp only [Setup.Block.get?, Setup.Block.length, if_pos leftBound, if_pos rightBound, formula]

theorem periodic_zero_block_span (left right offset index : Nat) (values : Array Nat)
    (leftBound : offset + index < left * values.size) (rightBound : index < right * values.size)
    (aligned : offset % values.size = 0) :
    (Setup.Block.periodic left 0 values).get? (offset + index) =
      (Setup.Block.periodic right 0 values).get? index := by
  rw [periodic_zero_get _ _ _ leftBound, periodic_zero_get _ _ _ rightBound]
  have position : (offset + index) % values.size = index % values.size := by
    rw [Nat.add_mod, aligned, Nat.zero_add, Nat.mod_mod]
  rw [position]

def finiteBlockSpanCheck (source target : Setup.Block) (offset count : Nat) : Bool :=
  decide (count ≤ 256) && (List.finRange count).all
    (fun index => decide (source.get? (offset + index.val) = target.get? index.val))

theorem finite_block_span_sound (source target : Setup.Block) (offset count : Nat)
    (checked : finiteBlockSpanCheck source target offset count = true)
    (index : Nat) (bounded : index < count) :
    source.get? (offset + index) = target.get? index := by
  simp only [finiteBlockSpanCheck, Bool.and_eq_true] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.2 ⟨index, bounded⟩ (List.mem_finRange _))

def finiteBlockSpanRangeCheck (source target : Setup.Block) (offset first count : Nat) : Bool :=
  decide (count ≤ 32) && (List.finRange count).all
    (fun index => decide (source.get? (offset + (first + index.val)) = target.get? (first + index.val)))

theorem finite_block_span_range_sound (source target : Setup.Block) (offset first count : Nat)
    (checked : finiteBlockSpanRangeCheck source target offset first count = true)
    (index : Nat) (lower : first ≤ index) (upper : index < first + count) :
    source.get? (offset + index) = target.get? index := by
  simp only [finiteBlockSpanRangeCheck, Bool.and_eq_true] at checked
  have bounded : index - first < count := by omega
  have actual := of_decide_eq_true (List.all_eq_true.mp checked.2 ⟨index - first, bounded⟩ (List.mem_finRange _))
  have position : first + (index - first) = index := by omega
  simpa only [position] using actual

def blockTargetsFollow (source : Setup.Block) (offset : Nat) : List Setup.Block → Prop
  | [] => True
  | target :: rest =>
      (∀ index < target.length, source.get? (offset + index) = target.get? index) ∧
      blockTargetsFollow source (offset + target.length) rest

theorem block_targets_follow_get (source : Setup.Block) (targets : List Setup.Block)
    (offset : Nat) (follows : blockTargetsFollow source offset targets)
    (index : Nat) (bounded : index < (targets.map Setup.Block.length).sum) :
    Setup.getFromBlocks targets index = source.get? (offset + index) := by
  induction targets generalizing offset index with
  | nil => simp at bounded
  | cons target rest ih =>
    simp only [List.map_cons, List.sum_cons] at bounded
    change (∀ index < target.length, _) ∧ _ at follows
    by_cases inside : index < target.length
    · rw [Setup.getFromBlocks, if_pos inside]
      exact (follows.1 index inside).symm
    · rw [Setup.getFromBlocks, if_neg inside]
      have remaining := ih (offset + target.length) follows.2 (index - target.length) (by omega)
      have position : offset + target.length + (index - target.length) = offset + index := by omega
      simpa only [position] using remaining

theorem block_partitions_agree (sources : List Setup.Block) (targets : List (List Setup.Block))
    (checked : List.Forall₂ (fun source target =>
      (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets)
    (index : Nat) : Setup.getFromBlocks sources index = Setup.getFromBlocks targets.flatten index := by
  induction checked generalizing index with
  | nil => rfl
  | @cons source target rest tail agreement remaining ih =>
    rw [List.flatten_cons, Setup.getFromBlocks, getFromBlocks_append, agreement.1]
    by_cases inside : index < source.length
    · rw [if_pos inside, if_pos inside]
      have actual := block_targets_follow_get source target 0 agreement.2 index (by rw [agreement.1]; exact inside)
      simpa only [Nat.zero_add] using actual.symm
    · rw [if_neg inside, if_neg inside]
      exact ih _

end Airbender.Compiler
