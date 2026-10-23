import Airbender.Proofs.Trace.StateClocks

namespace Airbender.Trace.Proofs
variable {Kind : Type} [CircuitLayout Kind]
set_option warningAsError true

private def windowWeight (lower upper clock : Nat) : Nat :=
  min (clock / 4) (upper / 4) - min (clock / 4) (lower / 4)

theorem stride_window_weight {lower upper clock : Nat}
    (first : lower % 4 = 0) (last : upper % 4 = 0) (aligned : clock % 4 = 0)
    (ordered : lower ≤ upper) :
    windowWeight lower upper (clock + 4) = windowWeight lower upper clock +
      if lower ≤ clock ∧ clock < upper then 1 else 0 := by
  unfold windowWeight
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem sum_indicators {S : Type} (rows : List S) (selected : S → Bool) :
    (rows.map fun row => if selected row then 1 else 0).sum = rows.countP selected := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    split <;> omega

theorem native_window_count [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0)
    (ordered : lower ≤ upper)
    (afterInitial : (timeOfPair trace.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (timeOfPair trace.terminal.timestamp).value) :
    (trace.rows.filter fun row => decide
      (lower ≤ (decodeTimestamp row.assignment row.columns.initialTime).value ∧
        (decodeTimestamp row.assignment row.columns.initialTime).value < upper)).length =
      (upper - lower) / 4 := by
  let weight := fun state : PCState.State p => windowWeight lower upper (timeOfPair state.timestamp).value
  let selected := fun row : Row p Kind => decide
    (lower ≤ (decodeTimestamp row.assignment row.columns.initialTime).value ∧
      (decodeTimestamp row.assignment row.columns.initialTime).value < upper)
  have clocks := state_clock_inputs hp inverse constraints states initial aligned
  have advance : ∀ row ∈ trace.rows, weight row.finish = weight row.start + if selected row then 1 else 0 := by
    intro row member
    have step := ClockLaws.advance hp inverse trace.rom row (constraints row member) (clocks row member).1
    have rowAligned : (decodeTimestamp row.assignment row.columns.initialTime).value % 4 = 0 := by
      simpa [Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clocks row member).2
    change windowWeight lower upper (decodeTimestamp row.assignment row.columns.finalTime).value =
      windowWeight lower upper (decodeTimestamp row.assignment row.columns.initialTime).value + if selected row then 1 else 0
    rw [step, stride_window_weight first last rowAligned ordered]
    simp only [selected, decide_eq_true_eq]
  have totals : (trace.rows.map fun row => weight row.finish).sum =
      (trace.rows.map fun row => weight row.start).sum + trace.rows.countP selected := by
    have rewritten := List.map_congr_left advance
    rw [rewritten, List.sum_map_add, sum_indicators]
  have matching := (states.map weight).sum_eq
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def] at matching
  have startWeight : weight trace.initial = 0 := by
    dsimp [weight, windowWeight]
    simp only [Nat.min_def]
    split_ifs <;> omega
  have finishWeight : weight trace.terminal = (upper - lower) / 4 := by
    dsimp [weight, windowWeight]
    simp only [Nat.min_def]
    split_ifs <;> omega
  rw [startWeight, finishWeight, totals] at matching
  rw [← List.countP_eq_length_filter]
  change trace.rows.countP selected = _
  omega

theorem native_suffix_count [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {lower : Nat} (first : lower % 4 = 0)
    (afterInitial : (timeOfPair trace.initial.timestamp).value ≤ lower)
    (beforeTerminal : lower ≤ (timeOfPair trace.terminal.timestamp).value) :
    (trace.rows.filter fun row => decide
      (lower ≤ (decodeTimestamp row.assignment row.columns.initialTime).value)).length =
      ((timeOfPair trace.terminal.timestamp).value - lower) / 4 := by
  let weight := fun state : PCState.State p =>
    (timeOfPair state.timestamp).value / 4 - min ((timeOfPair state.timestamp).value / 4) (lower / 4)
  let selected := fun row : Row p Kind => decide (lower ≤ (decodeTimestamp row.assignment row.columns.initialTime).value)
  have clocks := state_clock_inputs hp inverse constraints states initial aligned
  have advance : ∀ row ∈ trace.rows, weight row.finish = weight row.start + if selected row then 1 else 0 := by
    intro row member
    have step := ClockLaws.advance hp inverse trace.rom row (constraints row member) (clocks row member).1
    have rowAligned : (decodeTimestamp row.assignment row.columns.initialTime).value % 4 = 0 := by
      simpa [Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clocks row member).2
    change (decodeTimestamp row.assignment row.columns.finalTime).value / 4 -
      min ((decodeTimestamp row.assignment row.columns.finalTime).value / 4) (lower / 4) = _
    rw [step]
    dsimp [weight, selected, Row.start, timeOfPair, rawPair, decodeTimestamp]
    simp only [Nat.min_def, decide_eq_true_eq]
    split_ifs <;> omega
  have totals : (trace.rows.map fun row => weight row.finish).sum =
      (trace.rows.map fun row => weight row.start).sum + trace.rows.countP selected := by
    rw [List.map_congr_left advance, List.sum_map_add, sum_indicators]
  have matching := (states.map weight).sum_eq
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def] at matching
  have startWeight : weight trace.initial = 0 := by dsimp [weight]; omega
  have finishWeight : weight trace.terminal = ((timeOfPair trace.terminal.timestamp).value - lower) / 4 := by
    dsimp [weight]
    simp only [Nat.min_def]
    split_ifs <;> omega
  rw [startWeight, finishWeight, totals] at matching
  rw [← List.countP_eq_length_filter]
  change trace.rows.countP selected = _
  omega

end Airbender.Trace.Proofs
