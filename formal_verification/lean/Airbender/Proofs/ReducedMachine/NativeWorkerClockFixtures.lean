import Airbender.Review.Circuits.ReducedMachine.WorkerClockFixtures
import Airbender.Proofs.Blake2Worker.NativePositiveRow
import Airbender.Proofs.ReducedMachine.NativeWorkerClockProgress

namespace Airbender.NativeWorkerClockFixtureProofs
open Airbender.NativeWorkerClockFixtures Airbender.Verification
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Typed lookup bridge stays abstract BEFORE native literal-data instantiation. -/
private theorem table_lookup (setup : Table F (fields 4)) (entries : Vector (Expression F) 4) (w : Nat → F) :
    (Lookup.mk setup.toRaw entries).Contains (environment w) ↔ setup.Contains #[] (entries.map (Expression.eval (environment w))) := by
  simp [Lookup.Contains,Table.toRaw,environment,ProvableType.fromElements]
private theorem fixed_lookup (kind : Fixed.Kind) (entries : Vector (Expression F) 4) (w : Nat → F)
    (computed : entries.map (Expression.eval (environment w)) = #v[0,0,0,(kind.tag : F)]) :
    (Lookup.mk Fixed.table.toRaw entries).Contains (environment w) := by
  apply (table_lookup Fixed.table entries w).mpr
  rw [computed]
  exact PositiveRowProofs.zero_member kind

private theorem assertions0 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock0 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock0,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions1 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock1 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock1,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions2 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock2 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock2,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions3 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock3 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock3,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions4 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock4 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock4,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

private theorem assertions5 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    ((constraintsBlock5 Fixed.table).take 32) := by
  cases zeroClock <;> simp only [constraintsBlock5,List.take,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
private theorem lookups5 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    ((constraintsBlock5 Fixed.table).drop 32) := by
  cases zeroClock <;> simp only [constraintsBlock5,List.drop,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | trivial

private theorem lookups6 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock6 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock6,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply timestamp19_contains; decide +kernel)
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .three; decide +kernel)
    | (apply fixed_lookup .four; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups7 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock7 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock7,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .three; decide +kernel)
    | (apply fixed_lookup .four; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups8 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock8 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock8,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .three; decide +kernel)
    | (apply fixed_lookup .four; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups9 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock9 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock9,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem lookups10 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock))
    (constraintsBlock10 Fixed.table) := by
  cases zeroClock <;> simp only [constraintsBlock10,FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals first
    | trivial
    | (apply fixed_lookup .byte; decide +kernel)
    | (apply fixed_lookup .seven; decide +kernel)
    | (apply fixed_lookup .nine; decide +kernel)

private theorem block5 (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock)) (constraintsBlock5 Fixed.table) := by
  have combined := holds_append (assertions5 zeroClock) (lookups5 zeroClock)
  rw [List.take_append_drop] at combined
  exact combined

theorem body (zeroClock : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock)) (constraints Fixed.table) := by
  unfold constraints
  exact (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (holds_append (by trivial) (assertions0 zeroClock)) (assertions1 zeroClock)) (assertions2 zeroClock)) (assertions3 zeroClock)) (assertions4 zeroClock)) (block5 zeroClock)) (lookups6 zeroClock)) (lookups7 zeroClock)) (lookups8 zeroClock)) (lookups9 zeroClock)) (lookups10 zeroClock))

theorem local_processing (zeroClock : Bool) : LocalProcessingAccepted (assignment zeroClock) := by
  refine ⟨body zeroClock,?_⟩
  rw [ProcessingProofs.conventions_iff]
  change processingBitTerm 1 (assignment zeroClock 0) = 0 ∧ ∀ column ∈ ProcessingArtifact.processingMaskedColumns.toList,
    processingMaskTerm 1 (assignment zeroClock 0) (assignment zeroClock column) = 0
  have active : assignment zeroClock 0 = 1 := rfl
  simp [active,processingBitTerm,processingMaskTerm]

theorem multiplicity (zeroClock : Bool) : (assignment zeroClock) constraintsABI.multiplicity = 1 := rfl

theorem raw_clock (zeroClock : Bool) : Airbender.NativeActiveWorkerClocks.workerClock (assignment zeroClock) =
    (0,if zeroClock then 0 else 524288) := rfl

/-- Whole arithmetic-coordinate calculation BEFORE actual descriptor sampling. -/
theorem old_fields (zeroClock : Bool) (slot : Fin 43) :
    assignment zeroClock (743+3*slot.val) = 0 ∧
      assignment zeroClock (744+3*slot.val) = (if zeroClock then -1 else 0) := by
  have bound := slot.isLt
  have lo : ¬ (744 ≤ 743+3*slot.val ∧ 743+3*slot.val < 871 ∧ (743+3*slot.val-744)%3 = 0) := by omega
  have hi : 744 ≤ 744+3*slot.val ∧ 744+3*slot.val < 871 ∧ (744+3*slot.val-744)%3 = 0 := by omega
  constructor <;> simp [assignment,lo,hi,show 743+3*slot.val ≠ 741 by omega,
    show 744+3*slot.val ≠ 741 by omega]

theorem read_time (zeroClock : Bool) (slot : Fin 43) :
    (Airbender.NativeWorkerClockProgress.readToken (assignment zeroClock) slot).time =
      (0,if zeroClock then -1 else 0) := by
  rw [Airbender.NativeWorkerClockProgressProofs.read_time,(MemoryProofs.clock_columns slot).2]
  change (assignment zeroClock (743+3*slot.val),assignment zeroClock (744+3*slot.val)) = _
  rw [(old_fields zeroClock slot).1,(old_fields zeroClock slot).2]

theorem zero_old_unbounded (slot : Fin 43) :
    ¬ (Airbender.NativeWorkerClockProgress.readClock (assignment true) slot).Bounded :=
  Airbender.NativeWorkerClockProgressProofs.zero_unbounded (body true) (multiplicity true) (raw_clock true) slot

theorem wide_clock_unbounded : ¬ (Airbender.NativeWorkerClockProgress.clock (assignment false)).Bounded := by
  change ¬ ((Trace.timeOfPair (Airbender.NativeActiveWorkerClocks.workerClock (assignment false))).Bounded)
  rw [raw_clock]
  change ¬ ((0 : F).val < 524288 ∧ (524288 : F).val < 524288)
  decide +kernel

end Airbender.NativeWorkerClockFixtureProofs
