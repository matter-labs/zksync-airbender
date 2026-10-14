import Airbender.Review.Helpers.Context.Timestamps
import Mathlib.Data.List.Perm.Basic

namespace Airbender.Trace.Proofs

/-- State matching transfers native final-clock ranges to every incoming row;
    only the public initial clock needs a boundary bound. -/
theorem incoming_bounds {initial terminal : Timestamp} {steps : List (Timestamp × Timestamp)}
    (balanced : (initial :: steps.map Prod.snd).Perm (terminal :: steps.map Prod.fst))
    (initialBound : initial.Bounded)
    (finalBounds : ∀ step ∈ steps, step.2.Bounded) :
    ∀ step ∈ steps, step.1.Bounded := by
  intro step member
  have incoming : step.1 ∈ terminal :: steps.map Prod.fst :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨step, member, rfl⟩)
  have matched := balanced.mem_iff.mpr incoming
  rcases List.mem_cons.mp matched with boundaryMatch | outgoing
  · rw [boundaryMatch]
    exact initialBound
  · obtain ⟨previous, member, same⟩ := List.mem_map.mp outgoing
    rw [← same]
    exact finalBounds previous member

/-- Strict four-tick increments rule out a disconnected misaligned clock chain.
    Induction follows decreasing clock values, without assuming row order. -/
theorem incoming_alignment {initial terminal : Timestamp} {steps : List (Timestamp × Timestamp)}
    (balanced : (initial :: steps.map Prod.snd).Perm (terminal :: steps.map Prod.fst))
    (initialAligned : initial.value % 4 = 0)
    (advances : ∀ step ∈ steps, step.2.value = step.1.value + 4) :
    ∀ step ∈ steps, step.1.value % 4 = 0 := by
  have align : ∀ n : Nat, ∀ time ∈ steps.map Prod.fst,
      time.value = n → time.value % 4 = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro time member value
      have matched := balanced.mem_iff.mpr (List.mem_cons_of_mem terminal member)
      rcases List.mem_cons.mp matched with boundaryMatch | outgoing
      · simpa only [boundaryMatch] using initialAligned
      · obtain ⟨previous, member, same⟩ := List.mem_map.mp outgoing
        have increment := advances previous member
        have earlier : previous.1.value < n := by rw [same, value] at increment; omega
        have aligned := ih previous.1.value earlier previous.1
          (List.mem_map.mpr ⟨previous, member, rfl⟩) rfl
        rw [← same, increment]
        simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] using aligned
  intro step member
  exact align step.1.value step.1 (List.mem_map.mpr ⟨step, member, rfl⟩) rfl

/-- Every matched clock edge lies between the public endpoints. Strict native
    increments exclude disconnected chains; no list order is assumed. -/
theorem clock_interval {initial terminal : Timestamp} {steps : List (Timestamp × Timestamp)}
    (balanced : (initial :: steps.map Prod.snd).Perm (terminal :: steps.map Prod.fst))
    (advances : ∀ step ∈ steps, step.2.value = step.1.value + 4) :
    ∀ step ∈ steps, initial.value ≤ step.1.value ∧ step.2.value ≤ terminal.value := by
  have floor : ∀ n : Nat, ∀ time ∈ steps.map Prod.fst,
      time.value = n → initial.value ≤ time.value := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro time member value
      have matched := balanced.mem_iff.mpr (List.mem_cons_of_mem terminal member)
      rcases List.mem_cons.mp matched with same | outgoing
      · exact same ▸ Nat.le_refl _
      · obtain ⟨previous, member, same⟩ := List.mem_map.mp outgoing
        have increment := advances previous member
        rw [same] at increment
        have earlier := ih previous.1.value (by omega) previous.1
          (List.mem_map.mpr ⟨previous, member, rfl⟩) rfl
        omega
  let total := ((steps.map Prod.snd).map Timestamp.value).sum
  have ceiling : ∀ n : Nat, ∀ time ∈ steps.map Prod.snd,
      total - time.value = n → time.value ≤ terminal.value := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro time member value
      have matched := balanced.mem_iff.mp (List.mem_cons_of_mem initial member)
      rcases List.mem_cons.mp matched with same | incoming
      · exact same ▸ Nat.le_refl _
      · obtain ⟨next, member, same⟩ := List.mem_map.mp incoming
        have increment := advances next member
        rw [same] at increment
        have nextMember : next.2 ∈ steps.map Prod.snd := List.mem_map.mpr ⟨next, member, rfl⟩
        have bound : next.2.value ≤ total := List.le_sum_of_mem (List.mem_map.mpr ⟨next.2, nextMember, rfl⟩)
        have later := ih (total - next.2.value) (by omega) next.2 nextMember rfl
        omega
  intro step member
  exact ⟨floor _ _ (List.mem_map.mpr ⟨step, member, rfl⟩) rfl,
    ceiling _ _ (List.mem_map.mpr ⟨step, member, rfl⟩) rfl⟩

theorem low_alignment {time : Timestamp} (aligned : time.value % 4 = 0) : time.lo % 4 = 0 := by
  simpa [Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using aligned

/-- Matching states fixes the terminal clock from the actual number of rows. -/
theorem terminal_clock {initial terminal : Timestamp} {steps : List (Timestamp × Timestamp)}
    (balanced : (initial :: steps.map Prod.snd).Perm (terminal :: steps.map Prod.fst))
    (advances : ∀ step ∈ steps, step.2.value = step.1.value + 4) :
    terminal.value = initial.value + 4 * steps.length := by
  have sums := (balanced.map Timestamp.value).sum_eq
  simp only [List.map_cons, List.map_map, List.sum_cons] at sums
  have difference : (steps.map (fun step => step.2.value)).sum =
      (steps.map (fun step => step.1.value)).sum + 4 * steps.length := by
    clear balanced sums
    induction steps with
    | nil => simp
    | cons step rest ih =>
      have head := advances step (by simp)
      have tail := ih (fun step member => advances step (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [head, tail]
      omega
  change initial.value + (steps.map (fun step => step.2.value)).sum =
    terminal.value + (steps.map (fun step => step.1.value)).sum at sums
  rw [difference] at sums
  omega

end Airbender.Trace.Proofs
