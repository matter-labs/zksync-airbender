module
public import Proven.NonVacuous.SequentialRun

@[expose] public section

/-! Three more facts of a sequential run (`SequentialRun.lean`): runs from memories agreeing on the run's keys agree,
    consecutive blocks of a run compose, and a run followed by a second run from a memory agreeing with the first
    run's end is one run (`joint_matching`: the callers' machine steps, then a worker span). -/

namespace Airbender.NonVacuous

section Run
open scoped List
variable {α β : Type} [DecidableEq β]

/-- Runs from memories agreeing on the run's keys read the same values, and end agreeing on those keys. -/
theorem run_congr {mem other : β → α} {steps : List (β × α)}
    (same : ∀ key ∈ steps.map Prod.fst, mem key = other key) :
    runEdges mem steps = runEdges other steps ∧
      ∀ key ∈ steps.map Prod.fst, runFinal mem steps key = runFinal other steps key := by
  induction steps generalizing mem other with
  | nil => exact ⟨rfl, fun _ member => by cases member⟩
  | cons step rest ih =>
    obtain ⟨key, write⟩ := step
    have agree : ∀ k ∈ rest.map Prod.fst, Function.update mem key write k = Function.update other key write k := by
      intro k member
      by_cases equal : k = key
      · subst equal
        simp only [Function.update_self]
      · simp only [Function.update_of_ne equal]
        exact same k (List.mem_cons_of_mem _ member)
    obtain ⟨edges, final⟩ := ih agree
    refine ⟨?_, fun k member => ?_⟩
    · simp only [runEdges, same key (List.mem_cons_self ..), edges]
    · simp only [runFinal]
      by_cases later : k ∈ rest.map Prod.fst
      · exact final k later
      · rw [runFinal_of_not_mem _ later, runFinal_of_not_mem _ later]
        have equal : k = key := by
          rcases List.mem_cons.mp member with h | h
          · exact h
          · exact absurd h later
        subst equal
        simp only [Function.update_self]

/-- A run of consecutive blocks: block `k` runs from the memory `mem k` and leaves `mem (k + 1)`, its edges given by
    `edges k`; then the blocks' edges are the run's edges and the run ends at `mem n`. -/
theorem run_blocks {mem : Nat → β → α} {steps : Nat → List (β × α)} {edges : Nat → List (α × α)} (n : Nat)
    (next : ∀ k < n, runFinal (mem k) (steps k) = mem (k + 1))
    (each : ∀ k < n, edges k = runEdges (mem k) (steps k)) :
    (List.range n).flatMap edges = runEdges (mem 0) ((List.range n).flatMap steps) ∧
      runFinal (mem 0) ((List.range n).flatMap steps) = mem n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨edges', final⟩ := ih (fun k h => next k (by omega)) (fun k h => each k (by omega))
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      runEdges_append, runFinal_append, final, edges', each n (by omega), next n (by omega), and_self]

/-- A first run (`machine`, over `keys`) then a second run (`span`, over `cells ⊆ keys`) from a memory `m0` agreeing
    with the first run's end on `cells`: the seed of `keys` and the writes of both are a permutation of the final
    values and the reads, the second run's edges given by `blocks`. -/
theorem joint_matching {keys cells : List β} (nodup : keys.Nodup) (sub : ∀ c ∈ cells, c ∈ keys)
    {seed m0 : β → α} {machine span : List (β × α)} {edges spanEdges : List (α × α)}
    (run : edges = runEdges seed machine) (inside : ∀ step ∈ machine, step.1 ∈ keys)
    (agree : ∀ c ∈ cells, runFinal seed machine c = m0 c) (spanInside : ∀ step ∈ span, step.1 ∈ cells)
    (blocks : spanEdges = runEdges m0 span) :
    (keys.map seed ++ (edges ++ spanEdges).map Prod.snd).Perm
      (keys.map (runFinal (runFinal seed machine) span) ++ (edges ++ spanEdges).map Prod.fst) := by
  have whole := run_matching nodup seed (steps := machine ++ span) fun step member => by
    rcases List.mem_append.mp member with early | late
    · exact inside step early
    · exact sub _ (spanInside step late)
  have same := (run_congr (mem := runFinal seed machine) (other := m0) (steps := span) fun key member => by
    obtain ⟨step, present, rfl⟩ := List.mem_map.mp member
    exact agree _ (spanInside step present)).1
  rw [runEdges_append, runFinal_append, same, ← blocks, ← run] at whole
  exact whole

end Run

end Airbender.NonVacuous
