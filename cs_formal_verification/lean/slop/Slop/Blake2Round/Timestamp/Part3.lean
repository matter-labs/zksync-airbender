import Human.Circuits.Blake2Round.Artifact
import Slop.Blake2Round.ArtifactChecks
import Slop.Delegation.ClockFacts

namespace Airbender.Blake2Round.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
-- a port range's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

/-- Delegation clock comparisons for timestamp ports 18 to 23. -/
theorem clock_ports_3 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (i : Fin 43) (lowerIndex : 18 ≤ i.val) (upperIndex : i.val < 24) :
    w (Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val] (742 + 3 * i.val)).borrow * (w (Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val] (742 + 3 * i.val)).borrow - 1) = 0 ∧
    ((w (Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val] (742 + 3 * i.val)).previous[0] - w importedConstraintsDelegationColumns.invocation[0] -
      (Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val] (742 + 3 * i.val)).offset + Trace.timestampBase * w (Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val] (742 + 3 * i.val)).borrow) : ZMod p).val < Trace.timestampBase ∧
    ((w (Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val] (742 + 3 * i.val)).previous[1] + Trace.timestampBase - w (Trace.TimestampPort.mk 2 #v[740 + 3 * i.val, 741 + 3 * i.val] (742 + 3 * i.val)).borrow -
      w importedConstraintsDelegationColumns.invocation[1]) : ZMod p).val < Trace.timestampBase := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  have bit := Verification.assertion_of_holds core
    ⟨309 + i.val, by rw [constraint_count]; omega⟩
  have lowerLookup := Verification.lookup_of_holds timestamps
    ⟨2 + 2 * i.val, by rw [timestamp_count]; omega⟩
  have upperLookup := Verification.lookup_of_holds timestamps
    ⟨3 + 2 * i.val, by rw [timestamp_count]; omega⟩
  fin_cases i
  all_goals try (simp at lowerIndex upperIndex; done)
  all_goals have lower := Trace.Proofs.range_bound lowerLookup
  all_goals have upper := Trace.Proofs.range_bound upperLookup
  all_goals simp [importedConstraints, importedConstraintsDelegationColumns, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      sub_eq_add_neg, Trace.timestampBase] at bit lower upper ⊢
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | simpa only [add_comm] using bit
    | solve | convert lower using 1; congr 1; ring
    | solve | convert upper using 1; congr 1; ring

end Airbender.Blake2Round.Proofs
