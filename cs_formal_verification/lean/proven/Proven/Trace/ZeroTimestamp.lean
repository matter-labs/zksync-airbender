module
public import Proven.Trace.History

@[expose] public section

/-! Every row write of an accepted trace happens at or after the trace's initial clock. -/

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

/-- Strict four-tick increments put every incoming clock at or after the initial one.
    Same induction as `incoming_alignment`, along decreasing clock values. -/
theorem incoming_lower_bound {initial terminal : Timestamp} {steps : List (Timestamp × Timestamp)}
    (balanced : (initial :: steps.map Prod.snd).Perm (terminal :: steps.map Prod.fst))
    (advances : ∀ step ∈ steps, step.2.value = step.1.value + 4) :
    ∀ step ∈ steps, initial.value ≤ step.1.value := by
  have lower : ∀ n : Nat, ∀ time ∈ steps.map Prod.fst, time.value = n → initial.value ≤ time.value := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro time member value
      have matched := balanced.mem_iff.mpr (List.mem_cons_of_mem terminal member)
      rcases List.mem_cons.mp matched with boundaryMatch | outgoing
      · rw [boundaryMatch]
      · obtain ⟨previous, member, same⟩ := List.mem_map.mp outgoing
        have increment := advances previous member
        have earlier : previous.1.value < n := by rw [same, value] at increment; omega
        have bound := ih previous.1.value earlier previous.1
          (List.mem_map.mpr ⟨previous, member, rfl⟩) rfl
        rw [← same, increment]
        omega
  intro step member
  exact lower step.1.value step.1 (List.mem_map.mpr ⟨step, member, rfl⟩) rfl

/-- Every write token of an accepted trace has a clock at or after the initial clock: a row writes at its start
    clock plus a port offset below four, and matching chains each start clock back to the initial one. -/
theorem writes_after_initial [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (initialBound : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ row ∈ trace.rows, ∀ token ∈ row.writes,
      (timeOfPair trace.initial.timestamp).value ≤ (timeOfPair token.time).value := by
  -- the balanced clock multiset of `clock_matching` (private in `History.lean`)
  have matching : (timeOfPair trace.initial.timestamp :: (clockSteps trace).map Prod.snd).Perm
      (timeOfPair trace.terminal.timestamp :: (clockSteps trace).map Prod.fst) := by
    simpa [clockSteps, List.map_map, Function.comp_def, Row.start, Row.finish,
      timeOfPair, rawPair, decodeTimestamp] using
      accepted.states.map (fun state => timeOfPair state.timestamp)
  have finalBounds : ∀ step ∈ clockSteps trace, step.2.Bounded := by
    intro step member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact ClockLaws.finalBound trace.rom row (accepted.constraints row rowMember)
  have initialBounds := incoming_bounds matching initialBound finalBounds
  have advances : ∀ step ∈ clockSteps trace, step.2.value = step.1.value + 4 := by
    intro step member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact ClockLaws.advance hp inverse trace.rom row (accepted.constraints row rowMember)
      (initialBounds _ member)
  have alignments := incoming_alignment matching initialAligned advances
  have lower := incoming_lower_bound matching advances
  intro row member token writeMember
  have step : (decodeTimestamp row.assignment row.columns.initialTime,
      decodeTimestamp row.assignment row.columns.finalTime) ∈ clockSteps trace :=
    List.mem_map.mpr ⟨row, member, rfl⟩
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp writeMember
  have offsetBound := port_offset row port (by simpa using portMember)
  have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
    (initialBounds _ step) (low_alignment (alignments _ step)) offsetBound).2
  have start := lower _ step
  simp only [writeToken]
  change (timeOfPair trace.initial.timestamp).value ≤
    (timeOfPair ((rawPair row.assignment row.columns.initialTime).1 + (port.clock.offset : ZMod p),
      (rawPair row.assignment row.columns.initialTime).2)).value
  rw [time]
  exact start.trans (Nat.le_add_right _ _)

/-- Under the native boot boundary every write clock is at least four. -/
theorem boot_writes_after_four [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {Kind : Type} [CircuitLayout Kind] [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p Kind} (accepted : Accepted trace) (boot : trace.initial = PCState.boundary 0 (4, 0)) :
    ∀ row ∈ trace.rows, ∀ token ∈ row.writes, 4 ≤ (timeOfPair token.time).value := by
  have four : (timeOfPair trace.initial.timestamp).value = 4 ∧
      (timeOfPair trace.initial.timestamp).Bounded := by
    have lo : ((4 : ZMod p)).val = 4 := by exact_mod_cast ZMod.val_natCast_of_lt (n := p) (a := 4) (by omega)
    rw [boot]
    simp only [PCState.boundary, timeOfPair, Timestamp.value, Timestamp.Bounded, lo, ZMod.val_zero]
    norm_num [timestampBase]
  intro row member token writeMember
  have bound := writes_after_initial hp inverse accepted four.2 (by rw [four.1]) row member token writeMember
  omega

/-- A delegation-style write (invocation clock plus `offset`, with room in the low limb) has clock at least
    `offset`. -/
theorem invocation_write_after [Fact p.Prime] (hp : timestampBase < p) {w : Nat → ZMod p}
    {columns : Vector Nat 2} {offset : Nat}
    (room : (decodeTimestamp w columns).lo + offset < timestampBase)
    (high : (decodeTimestamp w columns).hi < timestampBase) :
    offset ≤ (timeOfPair ((rawPair w columns).1 + (offset : ZMod p), (rawPair w columns).2)).value := by
  change (timeOfPair (rawPair w columns)).lo + offset < timestampBase at room
  have time := (write_time_of_room hp (base := rawPair w columns) ⟨by omega, high⟩ room).2
  omega

end Airbender.Trace.Proofs
