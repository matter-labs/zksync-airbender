import Init.Data.List.Monadic
import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Airbender.Setup
open Lean
set_option warningAsError true
set_option Elab.async false

private theorem list_forIn_sum (blocks : List Block)
    (step : Block → Nat → Except String (ForInStep Nat))
    (sound : ∀ block initial result, step block initial = .ok result →
      result = .yield (initial + block.length))
    (initial final : Nat) (checked : forIn blocks initial step = .ok final) :
    final = initial + (blocks.map Block.length).sum := by
  induction blocks generalizing initial final with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure] at checked
    cases checked
    rfl
  | cons block rest ih =>
    rw [List.forIn_cons] at checked
    cases result : step block initial with
    | error error =>
      simp only [result, bind, Except.bind] at checked
      contradiction
    | ok next =>
      have same := sound block initial next result
      subst next
      simp only [result, bind, Except.bind] at checked
      have next := ih _ _ checked
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using next

private theorem array_forIn_sum (blocks : Array Block)
    (step : Block → Nat → Except String (ForInStep Nat))
    (sound : ∀ block initial result, step block initial = .ok result →
      result = .yield (initial + block.length))
    (initial final : Nat) (checked : forIn blocks initial step = .ok final) :
    final = initial + (blocks.toList.map Block.length).sum := by
  apply list_forIn_sum blocks.toList step sound initial final
  simpa only [Array.forIn_toList] using checked

theorem Column.length_of_validate (column : Column) (length bound : Nat)
    (checked : column.validate length bound = .ok ()) :
    (column.blocks.toList.map Block.length).sum = length := by
  unfold Column.validate at checked
  simp only [bind, Except.bind] at checked
  split at checked
  · contradiction
  · rename_i covered loop
    have total : covered = 0 + (column.blocks.toList.map Block.length).sum := by
      apply array_forIn_sum column.blocks _ ?_ 0 covered loop
      intro block initial result checkedStep
      simp only [pure, Except.pure] at checkedStep
      repeat' split at checkedStep
      all_goals first | contradiction | cases checkedStep; rfl
    split at checked
    · rename_i equal
      have same : covered = length := by simpa only [beq_iff_eq] using equal
      omega
    · contradiction

private theorem list_forIn_validated (columns : List Column) (validate : Column → Except String Unit)
    (checked : forIn columns PUnit.unit (fun column _ => do
      validate column
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ column ∈ columns, validate column = .ok () := by
  induction columns with
  | nil => simp
  | cons head rest ih =>
    rw [List.forIn_cons] at checked
    cases result : validate head with
    | error error =>
      simp only [result, bind, Except.bind] at checked
      contradiction
    | ok value =>
      cases value
      simp only [result, bind, Except.bind, pure, Except.pure] at checked
      intro column member
      cases member with
      | head => exact result
      | tail _ member => exact ih checked column member

private theorem array_forIn_validated (columns : Array Column) (validate : Column → Except String Unit)
    (checked : forIn columns PUnit.unit (fun column _ => do
      validate column
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ column ∈ columns, validate column = .ok () := by
  have listChecked := list_forIn_validated columns.toList validate
    (by simpa only [Array.forIn_toList] using checked)
  intro column member
  exact listChecked column (by simpa using member)

private theorem except_throw {α : Type} (error : String) :
    (throw error : Except String α) = .error error := rfl

theorem Artifact.columns_of_validate (artifact : Artifact) (checked : artifact.validate = .ok ()) :
    ∀ column ∈ artifact.columns, column.validate artifact.trace_len artifact.field_modulus = .ok () := by
  unfold Artifact.validate at checked
  simp only [except_throw, bind, Except.bind, pure, Except.pure] at checked
  repeat' split at checked
  all_goals first
    | contradiction
    | apply array_forIn_validated artifact.columns _
      assumption

theorem validate_of_parse {source : String} {artifact : Artifact}
    (checked : parse source = .ok artifact) : artifact.validate = .ok () := by
  unfold parse at checked
  simp only [bind, Except.bind, pure, Except.pure] at checked
  repeat' split at checked
  all_goals first
    | contradiction
    | cases checked
      assumption

end Airbender.Setup
