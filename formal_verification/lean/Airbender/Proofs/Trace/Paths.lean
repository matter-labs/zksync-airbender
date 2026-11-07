import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Clean.Utils.SourceSinkPath
import Airbender.Proofs.Trace.StateClocks

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]
noncomputable section
open Utils.StateTransition

def countedRun {S : Type} [DecidableEq S] (steps : List (S × S)) : Run S :=
  fun edge => steps.count edge

private theorem counted_flow {S : Type} [Fintype S] [DecidableEq S]
    (steps : List (S × S)) (state : S) :
    (countedRun steps).netFlow state =
      ((steps.map Prod.fst).count state : Int) - (steps.map Prod.snd).count state := by
  have first := sum_count_pairs_fst steps state
  have second := sum_count_pairs_snd steps state
  have firstMap : (steps.map Prod.fst).count state = steps.countP (fun edge => edge.1 = state) := by
    simp only [List.count_eq_countP, List.countP_map, Function.comp_def]
    rfl
  have secondMap : (steps.map Prod.snd).count state = steps.countP (fun edge => edge.2 = state) := by
    simp only [List.count_eq_countP, List.countP_map, Function.comp_def]
    rfl
  simp only [Run.netFlow, countedRun, ← Nat.cast_sum, first, second, firstMap, secondMap]

theorem matched_flow {S : Type} [Fintype S] [DecidableEq S]
    {steps : List (S × S)} {initial terminal : S}
    (matched : (initial :: steps.map Prod.snd).Perm (terminal :: steps.map Prod.fst))
    (state : S) : (countedRun steps).netFlow state =
      (if state = initial then 1 else 0) - (if state = terminal then 1 else 0) := by
  have counts := matched.count_eq state
  have initialSym : initial = state ↔ state = initial := eq_comm
  have terminalSym : terminal = state ↔ state = terminal := eq_comm
  simp only [List.count_cons, beq_iff_eq, initialSym, terminalSym] at counts
  rw [counted_flow]
  split_ifs at counts ⊢ <;> omega

private theorem path_increases {S : Type} (rank : S → Nat) (path : List S)
    (ascending : ∀ edge ∈ path.zip path.tail, rank edge.1 < rank edge.2) :
    ∀ first last, path.head? = some first → path.getLast? = some last →
      2 ≤ path.length → rank first < rank last := by
  revert ascending
  induction path with
  | nil => simp
  | cons start rest ih =>
    intro ascending first last head lastEq length
    have headEq : start = first := by simpa using head
    subst first
    cases rest with
    | nil => simp at length
    | cons next tail =>
      have firstEdge := ascending (start, next) (by simp)
      have tailAscending : ∀ edge ∈ (next :: tail).zip tail,
          rank edge.1 < rank edge.2 := by
        intro edge member
        exact ascending edge (by simpa using Or.inr member)
      cases tail with
      | nil =>
        have same : next = last := by simpa using lastEq
        simpa only [← same] using firstEdge
      | cons third tail =>
        have later := ih tailAscending next last rfl (by simpa using lastEq) (by simp)
        exact Nat.lt_trans firstEdge later

theorem increasing_acyclic {S : Type} [DecidableEq S] (run : Run S) (rank : S → Nat)
    (increases : ∀ edge, 0 < run edge → rank edge.1 < rank edge.2) : run.isAcyclic := by
  rintro ⟨cycle, length, endpoints, supported⟩
  have ascending : ∀ edge ∈ cycle.zip cycle.tail, rank edge.1 < rank edge.2 := by
    intro edge member
    exact increases edge (lt_of_lt_of_le (List.count_pos_iff.mpr member) (supported edge))
  cases cycle with
  | nil => simp at length
  | cons first rest =>
    have lastEq : (first :: rest).getLast? = some first := endpoints.symm
    have impossible := path_increases rank _ ascending first first rfl lastEq length
    exact Nat.lt_irrefl _ impossible

private theorem ascending_pairwise {S : Type} (rank : S → Nat) (path : List S)
    (ascending : ∀ edge ∈ path.zip path.tail, rank edge.1 < rank edge.2) :
    path.Pairwise (fun a b => rank a < rank b) := by
  revert ascending
  induction path with
  | nil => simp
  | cons first rest ih =>
    intro ascending
    cases rest with
    | nil => simp
    | cons next tail =>
      have firstEdge := ascending (first, next) (by simp)
      have restAscending : ∀ edge ∈ (next :: tail).zip tail,
          rank edge.1 < rank edge.2 := by
        intro edge member
        exact ascending edge (by simpa using Or.inr member)
      have restPairwise := ih restAscending
      refine List.pairwise_cons.mpr ⟨?_, restPairwise⟩
      intro later member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact firstEdge
      · exact Nat.lt_trans firstEdge (List.rel_of_pairwise_cons restPairwise inTail)

theorem rank_ordered {S : Type} (rank : S → Nat) (path : List S)
    (ascending : ∀ edge ∈ path.zip path.tail, rank edge.1 < rank edge.2) :
    (path.map rank).Pairwise (· < ·) :=
  List.pairwise_map.mpr (ascending_pairwise rank path ascending)

theorem rank_unique {S : Type} (rank : S → Nat) (path : List S)
    (ascending : ∀ edge ∈ path.zip path.tail, rank edge.1 < rank edge.2) :
    (path.map rank).Nodup := by
  have strict := rank_ordered rank path ascending
  exact strict.imp Nat.ne_of_lt

private theorem path_flow {S : Type} [Fintype S] [DecidableEq S] (path : List S) (state : S) :
    Run.netFlow (fun edge => countTransitionInPath edge path) state =
      (if path.head? = some state then 1 else 0) -
        (if path.getLast? = some state then 1 else 0) := by
  have counts := countAsFirst_add_last_eq_countAsSecond_add_head path state
  simp only [Run.netFlow, sum_countTransitionInPath_fst, sum_countTransitionInPath_snd]
  split_ifs at counts ⊢ <;> omega

private theorem zero_flow_empty {S : Type} [Fintype S] [DecidableEq S] (run : Run S)
    (acyclic : run.isAcyclic) (balanced : ∀ state, run.netFlow state = 0) :
    ∀ edge, run edge = 0 := by
  intro edge
  by_contra nonzero
  have positive : 0 < run edge := Nat.pos_of_ne_zero nonzero
  have outgoing : ∃ next, 0 < run (edge.1, next) := ⟨edge.2, positive⟩
  obtain ⟨leaf, leafProperty⟩ := acyclic_has_leaf run edge.1 acyclic outgoing
  have negative := leaf_has_incoming_and_negative_netFlow run edge.1 leaf leafProperty outgoing
  rw [balanced leaf] at negative
  omega

/-- Clean supplies a simple source/sink path. Strict ranks and balanced native
    counts additionally show that it consumes every transition, not just a subset. -/
theorem matched_path {S : Type} [Fintype S] [DecidableEq S]
    {steps : List (S × S)} {initial terminal : S} (rank : S → Nat)
    (matched : (initial :: steps.map Prod.snd).Perm (terminal :: steps.map Prod.fst))
    (increases : ∀ edge ∈ steps, rank edge.1 < rank edge.2) :
    ∃ path : List S, path.head? = some initial ∧ path.getLast? = some terminal ∧
      path.Nodup ∧ ∀ edge, countTransitionInPath edge path = (countedRun steps) edge := by
  let run := countedRun steps
  have ascending : ∀ edge, 0 < run edge → rank edge.1 < rank edge.2 := by
    intro edge positive
    exact increases edge (List.count_pos_iff.mp positive)
  have acyclic := increasing_acyclic run rank ascending
  by_cases same : initial = terminal
  · have empty := zero_flow_empty run acyclic (by intro state; simpa [same] using matched_flow matched state)
    refine ⟨[initial], rfl, ?_, by simp, ?_⟩
    · simpa using congrArg some same
    · intro edge
      simp only [countTransitionInPath, List.tail_cons, List.zip_nil_right, List.count_nil]
      exact (empty edge).symm
  · have source : run.netFlow initial = 1 := by simpa [same] using matched_flow matched initial
    have others : ∀ state, state ≠ initial → state ≠ terminal → run.netFlow state = 0 := by
      intro state hi ht
      simpa [hi, ht] using matched_flow matched state
    obtain ⟨path, head, last, _, supported, nodup⟩ :=
      acyclic_run_has_path_from_source_to_sink run initial terminal acyclic source others
    let remainder : Run S := fun edge => run edge - countTransitionInPath edge path
    have remainderIncreases : ∀ edge, 0 < remainder edge → rank edge.1 < rank edge.2 := by
      intro edge positive
      exact ascending edge (lt_of_lt_of_le positive (Nat.sub_le _ _))
    have remainderFlow : ∀ state, remainder.netFlow state = 0 := by
      intro state
      rw [netFlow_sub run (fun edge => countTransitionInPath edge path) state supported,
        matched_flow matched, path_flow, head, last]
      have initialSym : initial = state ↔ state = initial := eq_comm
      have terminalSym : terminal = state ↔ state = terminal := eq_comm
      simp only [Option.some.injEq, initialSym, terminalSym]
      omega
    have empty := zero_flow_empty remainder (increasing_acyclic _ rank remainderIncreases) remainderFlow
    refine ⟨path, head, last, nodup, ?_⟩
    intro edge
    have zero := empty edge
    have capacity := supported edge
    dsimp only [remainder] at zero
    change countTransitionInPath edge path = run edge
    omega

private def stateEquiv (p : Nat) :
    ((ZMod p × ZMod p) × (ZMod p × ZMod p)) ≃ PCState.State p where
  toFun pair := ⟨pair.1, pair.2⟩
  invFun state := (state.pc, state.timestamp)
  left_inv _ := rfl
  right_inv state := by cases state; rfl

local instance [Fact p.Prime] : Fintype (PCState.State p) :=
  Fintype.ofEquiv _ (stateEquiv p)

local instance : DecidableEq (PCState.State p) := Classical.decEq _

/-- Instantiate Clean's path theorem with the actual imported state columns.
    Native clock advancement proves acyclicity; no execution order is assumed. -/
theorem state_path_checks [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    [ClockLaws Kind p] (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∃ path, StatePath trace path := by
  let steps := trace.rows.map fun row => (row.start, row.finish)
  let rank := fun state : PCState.State p => (timeOfPair state.timestamp).value
  have matching : (trace.initial :: steps.map Prod.snd).Perm
      (trace.terminal :: steps.map Prod.fst) := by
    simpa [steps, List.map_map, Function.comp_def] using states
  have clocks := state_clock_inputs hp inverse constraints states initial aligned
  have increases : ∀ edge ∈ steps, rank edge.1 < rank edge.2 := by
    intro edge member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    have step := ClockLaws.advance hp inverse trace.rom row (constraints row rowMember) (clocks row rowMember).1
    change (decodeTimestamp row.assignment row.columns.initialTime).value <
      (decodeTimestamp row.assignment row.columns.finalTime).value
    omega
  obtain ⟨path, head, last, _, counts⟩ := matched_path rank matching increases
  have permutation : (path.zip path.tail).Perm steps := List.perm_iff_count.mpr counts
  have clocksUnique : (path.map rank).Nodup := rank_unique rank path (by
    intro edge member
    exact increases edge (permutation.mem_iff.mp member))
  exact ⟨path, head, last, permutation, clocksUnique⟩

theorem native_state_path [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    [ClockLaws Kind p] (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∃ path, StatePath trace path :=
  state_path_checks hp inverse accepted.constraints accepted.states boundary.initial boundary.aligned

end
end Airbender.Trace.Proofs
