import Mathlib.Data.List.Forall2
import Mathlib.Logic.Function.Iterate

namespace Airbender.UnifiedReduced.Caller.Proofs.PathControl

set_option warningAsError true

/-! Generic controller paths retain every raw token edge. A refresh may change
metadata while preserving the selected value; an advance applies the controller
transition; an update records a separately derived computation. These lemmas do
not derive instruction effects, valid controls or whole-state frames. -/

universe u v

/-- Value actions for an occurrence path. An update is an explicit computation,
    not a reason to omit that edge from the path. -/
inductive Action (α : Type u) where
  | refresh
  | advance
  | update (compute : α → α)

/-- Project one already established raw-token transition to its value. -/
def Action.eval {α : Type u} (advance : α → α) : Action α → α → α
  | .refresh, value => value
  | .advance, value => advance value
  | .update compute, value => compute value

/-- Apply value actions in their actual occurrence order. -/
def run {α : Type u} (advance : α → α) : List (Action α) → α → α
  | [], value => value
  | action :: rest, value => run advance rest (action.eval advance value)

/-- Running concatenated occurrence intervals keeps the exact intervening value. -/
theorem run_append {α : Type u} (advance : α → α)
    (first second : List (Action α)) (value : α) :
    run advance (first ++ second) value = run advance second (run advance first value) := by
  induction first generalizing value with
  | nil => rfl
  | cons action rest ih =>
    change run advance (rest ++ second) (action.eval advance value) =
      run advance second (run advance rest (action.eval advance value))
    exact ih _

/-- A connected raw-token path. Only the selected projection is constrained;
    tokens on a refresh edge need not be equal. -/
inductive Follows {Token : Type u} {α : Type v}
    (project : Token → α) (advance : α → α) : Token → List (Action α) → Token → Prop where
  | nil (token : Token) : Follows project advance token [] token
  | cons {source middle target : Token} {action : Action α} {rest : List (Action α)}
      (step : project middle = action.eval advance (project source))
      (tail : Follows project advance middle rest target) :
      Follows project advance source (action :: rest) target

/-- Build the connected path from all adjacent raw-token edges in order.
    The supplied edge facts are generic local transitions; native instruction
    and matching adapters must establish them separately. -/
theorem Follows.of_edges {Token : Type u} {α : Type v}
    {project : Token → α} {advance : α → α} (source : Token) (rest : List Token)
    {actions : List (Action α)}
    (steps : List.Forall₂
      (fun action edge => project edge.2 = action.eval advance (project edge.1))
      actions ((source :: rest).zip rest)) :
    Follows project advance source actions (rest.getLastD source) := by
  induction rest generalizing source actions with
  | nil =>
    cases steps
    exact .nil source
  | cons middle rest ih =>
    cases steps with
    | cons step tail =>
      rw [List.getLastD_cons]
      exact .cons step (ih _ tail)

/-- The endpoint is computed by every edge, including explicit updates. -/
theorem Follows.projected {Token : Type u} {α : Type v}
    {project : Token → α} {advance : α → α} {source target : Token}
    {actions : List (Action α)} (path : Follows project advance source actions target) :
    project target = run advance actions (project source) := by
  induction path with
  | nil => rfl
  | cons step tail ih =>
    simpa only [run, ← step] using ih

/-- Composition connects the actual middle token, not merely equal PC labels. -/
theorem Follows.append {Token : Type u} {α : Type v}
    {project : Token → α} {advance : α → α} {source middle target : Token}
    {first second : List (Action α)}
    (left : Follows project advance source first middle)
    (right : Follows project advance middle second target) :
    Follows project advance source (first ++ second) target := by
  induction left generalizing second target with
  | nil => exact right
  | cons step tail ih => exact .cons step (ih right)

/-- Any occurrence cut has an actual intermediate raw token. -/
theorem Follows.split {Token : Type u} {α : Type v}
    {project : Token → α} {advance : α → α} {source target : Token}
    (first second : List (Action α))
    (path : Follows project advance source (first ++ second) target) :
    ∃ middle, Follows project advance source first middle ∧
      Follows project advance middle second target := by
  induction first generalizing source with
  | nil => exact ⟨source, .nil source, path⟩
  | cons action rest ih =>
    cases path with
    | cons step tail =>
      obtain ⟨middle, left, right⟩ := ih tail
      exact ⟨middle, .cons step left, right⟩

/-- Splitting also computes the value at the cut and at the final endpoint. -/
theorem Follows.cut {Token : Type u} {α : Type v}
    {project : Token → α} {advance : α → α} {source target : Token}
    (first second : List (Action α))
    (path : Follows project advance source (first ++ second) target) :
    ∃ middle, Follows project advance source first middle ∧
      Follows project advance middle second target ∧
      project middle = run advance first (project source) ∧
      project target = run advance second (project middle) := by
  obtain ⟨middle, left, right⟩ := Follows.split first second path
  exact ⟨middle, left, right, left.projected, right.projected⟩

/-- False marks a value refresh; true marks a controller advance. -/
def marked {α : Type u} (flags : List Bool) : List (Action α) :=
  flags.map fun flag => if flag then .advance else .refresh

/-- Count controller advances, independently of token refreshes. -/
def advanceCount : List Bool → Nat
  | [] => 0
  | false :: rest => advanceCount rest
  | true :: rest => advanceCount rest + 1

theorem marked_append {α : Type u} (first second : List Bool) :
    marked (α := α) (first ++ second) = marked first ++ marked second := by
  simp only [marked, List.map_append]

theorem advanceCount_append (first second : List Bool) :
    advanceCount (first ++ second) = advanceCount first + advanceCount second := by
  induction first with
  | nil => simp only [List.nil_append, advanceCount, Nat.zero_add]
  | cons flag rest ih =>
    cases flag
    · exact ih
    · simp only [List.cons_append, advanceCount, ih,
        Nat.add_comm, Nat.add_left_comm]

/-- Refreshes retain their raw edges but do not consume a controller position. -/
theorem run_marked {α : Type u} (advance : α → α) (flags : List Bool) (value : α) :
    run advance (marked flags) value = advance^[advanceCount flags] value := by
  induction flags generalizing value with
  | nil => rfl
  | cons flag rest ih =>
    cases flag
    · change run advance (marked rest) value = advance^[advanceCount rest] value
      exact ih _
    · change run advance (marked rest) (advance value) =
        advance^[advanceCount rest + 1] value
      rw [ih]
      rfl

/-- A marked raw path derives its endpoint from the number of actual advances. -/
theorem Follows.marked_projected {Token : Type u} {α : Type v}
    {project : Token → α} {advance : α → α} {source target : Token}
    {flags : List Bool} (path : Follows project advance source (marked flags) target) :
    project target = advance^[advanceCount flags] (project source) := by
  exact path.projected.trans (run_marked advance flags _)

/-- Every marked occurrence prefix has its own actual cut token and derived
    controller value, even when many intervening edges only refresh timestamps. -/
theorem Follows.marked_cut {Token : Type u} {α : Type v}
    {project : Token → α} {advance : α → α} {source target : Token}
    (first second : List Bool)
    (path : Follows project advance source (marked (first ++ second)) target) :
    ∃ middle, Follows project advance source (marked first) middle ∧
      Follows project advance middle (marked second) target ∧
      project middle = advance^[advanceCount first] (project source) ∧
      project target = advance^[advanceCount second] (project middle) := by
  rw [marked_append] at path
  obtain ⟨middle, left, right⟩ := Follows.split (marked first) (marked second) path
  exact ⟨middle, left, right, left.marked_projected, right.marked_projected⟩

end Airbender.UnifiedReduced.Caller.Proofs.PathControl
