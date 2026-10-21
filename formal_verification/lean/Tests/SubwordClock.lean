import Tests.SubwordHistoryRows

namespace Tests.SubwordClock
open Airbender Verification Arithmetic Trace SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

abbrev rom := Tests.SubwordDecoderFixture.rom

/-- The same full ROM LB row at the last aligned low-limb clock. -/
def values : Array Nat := #[0,0,524284,0,1,1,0,3,0,0,0,0,0,4,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,32769,32769,1,3,0,0,0,65534,65535,33022,4660,33022,65534,65535,32769,0,98556,0,98556,0,0,33022,4660,46,33022,65534,65535,45,65534,65535,65534,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,1]
def rollover (column : Nat) : ZMod mersenne31Modulus := (values[column]?.getD 0 : Nat)

theorem native_constraints :
    FlatOperation.ConstraintsHoldFlat (environment rollover) (SubwordMemory.importedConstraints rom) := by
  simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, rollover, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) | (apply range16_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide +kernel) | skip
  · simp only [Lookup.Contains,fixed3,Table.toRaw,SubwordOffset.table,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨524288,by decide⟩,by decide +kernel⟩
  · simp only [Lookup.Contains,fixed3,Table.toRaw,romSeparatorTable,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨0,by decide⟩,by decide +kernel⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements,
      rollover,values,Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values]
      using Tests.SubwordDecoderFixture.lookup_members ⟨0,by decide⟩ ⟨0,by decide⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements,
      rollover,values,Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values]
      using Tests.SubwordDecoderFixture.lookup_members ⟨0,by decide⟩ ⟨1,by decide⟩

private theorem inputs : ClockInputs importedConstraintsTraceColumns rollover := by
  constructor
  · constructor <;> decide +kernel
  · decide +kernel
  · intro port member
    simp [importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide +kernel

theorem native_rollover :
    (decodeTimestamp rollover importedConstraintsTraceColumns.finalTime).lo = 0 ∧
    (decodeTimestamp rollover importedConstraintsTraceColumns.finalTime).hi = 1 ∧
    (decodeTimestamp rollover importedConstraintsTraceColumns.finalTime).value = 524288 := by
  have advance := SubwordMemory.Proofs.clock_advance (by decide) native_constraints inputs.initial
  have start : (decodeTimestamp rollover importedConstraintsTraceColumns.initialTime).value = 524284 := by
    decide +kernel
  exact ⟨by decide +kernel,by decide +kernel,by simpa only [start] using advance⟩

theorem native_port_order : ClockEffects importedConstraintsTraceColumns rollover :=
  SubwordMemory.Proofs.clock_effects (by decide) native_constraints inputs

def badCarry (column : Nat) : ZMod mersenne31Modulus := if column = 77 then 2 else rollover column

theorem nonboolean_carry_rejected : ¬FlatOperation.ConstraintsHoldFlat (environment badCarry)
    (SubwordMemory.importedConstraints rom) := by
  intro accepted
  have bit := Verification.assertion_of_holds accepted ⟨8,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  norm_num [SubwordMemory.importedConstraints,FlatOperation.constraints,Expression.eval,environment,badCarry] at bit
  exact (by decide +kernel : (2 : ZMod mersenne31Modulus) ≠ 0) bit

def badFinal (column : Nat) : ZMod mersenne31Modulus := if column = 16 then 524288 else rollover column

theorem overflowing_high_rejected : ¬FlatOperation.ConstraintsHoldFlat (environment badFinal)
    (SubwordMemory.importedConstraints rom) := by
  intro accepted
  have upper := (SubwordMemory.Proofs.final_clock_bound accepted).2
  exact (by decide +kernel : ¬(decodeTimestamp badFinal importedConstraintsTraceColumns.finalTime).hi < timestampBase) upper

end Tests.SubwordClock
