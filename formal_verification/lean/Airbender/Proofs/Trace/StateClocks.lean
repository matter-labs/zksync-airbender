import Airbender.Proofs.Trace.History

namespace Airbender.Trace.Proofs
variable {Kind : Type} [CircuitLayout Kind]
set_option warningAsError true

theorem state_clock_inputs [Fact p.Prime] [ClockLaws Kind p]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p Kind}
    (constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ row ∈ trace.rows,
      (decodeTimestamp row.assignment row.columns.initialTime).Bounded ∧
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0 := by
  have matching : (timeOfPair trace.initial.timestamp :: (clockSteps trace).map Prod.snd).Perm
      (timeOfPair trace.terminal.timestamp :: (clockSteps trace).map Prod.fst) := by
    simpa [clockSteps, List.map_map, Function.comp_def, Row.start, Row.finish,
      timeOfPair, rawPair, decodeTimestamp] using states.map (fun state => timeOfPair state.timestamp)
  have finalBounds : ∀ step ∈ clockSteps trace, step.2.Bounded := by
    intro step member
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
    exact ClockLaws.finalBound trace.rom row (constraints row present)
  have bounds := incoming_bounds matching initial finalBounds
  have advances : ∀ step ∈ clockSteps trace, step.2.value = step.1.value + 4 := by
    intro step member
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
    exact ClockLaws.advance hp inverse trace.rom row (constraints row present)
      (bounds _ (List.mem_map.mpr ⟨row, present, rfl⟩))
  have alignments := incoming_alignment matching aligned advances
  intro row present
  have member : (decodeTimestamp row.assignment row.columns.initialTime,
      decodeTimestamp row.assignment row.columns.finalTime) ∈ clockSteps trace :=
    List.mem_map.mpr ⟨row, present, rfl⟩
  exact ⟨bounds _ member, low_alignment (alignments _ member)⟩

end Airbender.Trace.Proofs
