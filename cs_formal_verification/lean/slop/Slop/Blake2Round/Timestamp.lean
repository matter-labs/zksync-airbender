import Slop.Blake2Round.Timestamp.Part0
import Slop.Blake2Round.Timestamp.Part1
import Slop.Blake2Round.Timestamp.Part2
import Slop.Blake2Round.Timestamp.Part3
import Slop.Blake2Round.Timestamp.Part4
import Slop.Blake2Round.Timestamp.Part5
import Slop.Blake2Round.Timestamp.Part6
import Slop.Blake2Round.Timestamp.Part7
import Human.Circuits.Blake2Round.Artifact
import Slop.Blake2Round.ArtifactChecks
import Slop.Delegation.ClockFacts

namespace Airbender.Blake2Round.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem clock_facts {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup)) :
    Delegation.Proofs.ClockFacts importedConstraintsDelegationColumns w := by
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  have low := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
    ⟨0, by rw [timestamp_count]; decide⟩)
  have high := Trace.Proofs.range_bound (Verification.lookup_of_holds timestamps
    ⟨1, by rw [timestamp_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at low high
  refine ⟨⟨low, high⟩, ?_, ?_⟩
  · intro port member
    rw [delegation_columns] at member
    simp only [Vector.toArray_ofFn, Array.mem_ofFn] at member
    obtain ⟨i, rfl⟩ := member
    change (2 : Nat) < 4
    decide
  · intro port member
    rw [delegation_columns] at member
    simp only [Vector.toArray_ofFn, Array.mem_ofFn] at member
    obtain ⟨i, rfl⟩ := member
    have size := i.isLt
    by_cases c0 : i.val < 6
    · exact clock_ports_0 h i (by omega) c0
    by_cases c1 : i.val < 12
    · exact clock_ports_1 h i (by omega) c1
    by_cases c2 : i.val < 18
    · exact clock_ports_2 h i (by omega) c2
    by_cases c3 : i.val < 24
    · exact clock_ports_3 h i (by omega) c3
    by_cases c4 : i.val < 30
    · exact clock_ports_4 h i (by omega) c4
    by_cases c5 : i.val < 36
    · exact clock_ports_5 h i (by omega) c5
    by_cases c6 : i.val < 42
    · exact clock_ports_6 h i (by omega) c6
    exact clock_ports_7 h i (by omega) size

end Airbender.Blake2Round.Proofs
