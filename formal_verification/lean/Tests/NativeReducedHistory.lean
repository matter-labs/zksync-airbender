import Airbender.Review.Trace.Families.ReducedMachine.History

namespace Tests.NativeReducedHistory
open Airbender Trace ReducedMachine Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The last aligned low limb carries into the high clock limb, without wrapping the epoch. -/
theorem low_clock_carry {w : Nat → ZMod mersenne31Modulus}
    {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (low : w 2 = 524284) (high : w 3 = 7) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).value = 4194304 := by
  have initial : (decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded := by
    change (w 2).val < 524288 ∧ (w 3).val < 524288
    rw [low,high]
    decide +kernel
  have advance := NativeClockProofs.clock_advance (by decide) holds initial
  have start : (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value = 4194300 := by
    change (w 2).val + 524288 * (w 3).val = 4194300
    rw [low,high]
    decide +kernel
  simpa only [start] using advance

/-- Native clock range enforcement rejects an exhausted epoch; RV32 PC wrap is separate. -/
theorem clock_epoch_overflow_rejected {w : Nat → ZMod mersenne31Modulus}
    {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (low : w 2 = 524284) (high : w 3 = 524287) : False := by
  have initial : (decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded := by
    change (w 2).val < 524288 ∧ (w 3).val < 524288
    rw [low,high]
    decide +kernel
  have advance := NativeClockProofs.clock_advance (by decide) holds initial
  have final := NativeClockProofs.final_clock_bound holds
  have start : (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value = 274877906940 := by
    change (w 2).val + 524288 * (w 3).val = 274877906940
    rw [low,high]
    decide +kernel
  rw [start] at advance
  change (w 15).val < 524288 ∧ (w 16).val < 524288 at final
  change (w 15).val + 524288 * (w 16).val = _ at advance
  omega

/-- Full initialized acceptance derives the port chronology; no prior-clock bound is supplied. -/
theorem nonpreceding_read_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows)
    (port : MemoryPort) (member : port ∈ row.ports)
    (nonpreceding : (decodeTimestamp row.assignment port.clock.previous).value ≥
      (decodeTimestamp row.assignment row.columns.initialTime).value + port.clock.offset) : False := by
  have effects := (Native.public_clock_soundness inputs accepted).2.1 row present
  have found : port.clock ∈ row.columns.ports := by
    rw [← Trace.Proofs.ports_clocks row]
    exact Array.mem_map.mpr ⟨port,member,rfl⟩
  have strict := (effects.accesses _ found).1
  omega

/-- The accepted terminal clock counts native rows even when all destination writes discard. -/
theorem wrong_terminal_steps_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (wrong : (timeOfPair trace.terminal.timestamp).value ≠
      (timeOfPair trace.initial.timestamp).value + 4 * trace.rows.length) : False :=
  wrong (Native.public_clock_soundness inputs accepted).2.2

end Tests.NativeReducedHistory
