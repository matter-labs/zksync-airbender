import Airbender.Proofs.FullUnsigned.CPUWriteRules
import Airbender.Proofs.Trace.StreamCount
import Airbender.Review.Helpers.Decoder.PooledExternalInput
import Airbender.Proofs.Reduced.CallerSources

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Native clocks give the exact external-input increment for every full CPU cycle. -/
theorem unrolled_full_cycle_count
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows) :
    ExternalStream.countBefore Trace.Row.clock NonDeterminism.Pooled.isRead trace.rows
        (timeOfPair row.finish.timestamp).value =
      ExternalStream.countBefore Trace.Row.clock NonDeterminism.Pooled.isRead trace.rows row.clock +
        (if NonDeterminism.Pooled.isRead row then 1 else 0) := by
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have time := ClockLaws.advance (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus) trace.rom row
    (accepted.cpuEquations row member) (clocks row member).1
  change (timeOfPair row.finish.timestamp).value = row.clock + 4 at time
  rw [time]
  apply ExternalStream.Proofs.count_after_cycle Trace.Row.clock NonDeterminism.Pooled.isRead member
    (state_clocks_unique (by decide) (by decide +kernel : SerializedInverse.Clock babyBearModulus)
      accepted.cpuEquations accepted.states initialClock initialAligned)
  intro item present
  simpa [Trace.Row.clock, decodeTimestamp, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
    using (clocks item present).2

/-- The public starting clock precedes every native full-trace external read. -/
theorem unrolled_full_initial_count
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ExternalStream.countBefore Trace.Row.clock NonDeterminism.Pooled.isRead trace.rows
      (timeOfPair trace.initial.timestamp).value = 0 := by
  have intervals := state_clock_interval (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  apply ExternalStream.Proofs.count_at_start
  intro row member
  exact (intervals row member).1

/-- The final full-trace clock accounts for every native external read once. -/
theorem unrolled_full_terminal_count
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ExternalStream.countBefore Trace.Row.clock NonDeterminism.Pooled.isRead trace.rows
      (timeOfPair trace.terminal.timestamp).value = NonDeterminism.Pooled.readCount trace := by
  have intervals := state_clock_interval (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  apply ExternalStream.Proofs.count_at_finish
  intro row member
  have bound := (intervals row member).2
  change row.clock + 4 ≤ (timeOfPair trace.terminal.timestamp).value at bound
  omega

/-- Both native standard and split callers leave the external stream position fixed. -/
theorem unrolled_full_caller_read_disabled
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment) :
    NonDeterminism.Pooled.isRead row = false := by
  have packed : (Delegation.Caller.nativeQuery row.assignment)[8] = (128 : ZMod babyBearModulus) := by
    rcases unrolled_full_native_row_classification setup lookup accepted excluded initialPC row member with
      ⟨_, _, _, _, _, ordinary⟩ | ⟨_, _, _, _, query, _⟩ | ⟨_, _, _, _, query, _⟩
    · exact False.elim (ordinary ⟨family, selected⟩)
    · exact congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[8]) query
    · exact congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[8]) query
  have core := accepted.cpuEquations row member
  simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at core
  have holds := Verification.holds_of_sublist core
    (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
  have flags := (AddSub.Proofs.local_flags holds).2
  have boolean : ∀ i : Fin 9,
      row.assignment #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
        row.assignment #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
    intro i
    have bit := flags i
    fin_cases i <;> simpa using bit
  change (∑ i : Fin 9, (2 ^ i.val : Nat) *
    row.assignment #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) = (128 : ZMod babyBearModulus) at packed
  have bits := unpack_decoder_bits (by decide : 512 < babyBearModulus) (by decide) boolean packed
  have zero : row.assignment 18 = 0 := bits 8
  simp [NonDeterminism.Pooled.isRead, family, NonDeterminism.isRead, zero]

end Airbender.Compiler.MachineTargets.Proofs
