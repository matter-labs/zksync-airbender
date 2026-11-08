import Human.Helpers.Context.Registries.ShiftBinop
import Slop.ShiftBinop.Timestamp
import Slop.Trace.RowHistory
import Slop.ShiftBinop

namespace Airbender.ShiftBinop

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := rfl

@[simp] theorem trace_decoder_columns (kind : TraceKind) :
    Trace.CircuitLayout.decoderColumns kind = importedConstraintsDecoderColumns := rfl

@[simp] theorem trace_constraints [Fact p.Prime] (kind : TraceKind)
    (rom : Table (ZMod p) (fields 9)) :
    Trace.CircuitLayout.constraints kind rom = clockConstraints := rfl

end Airbender.ShiftBinop

namespace Airbender.ShiftBinop.Proofs
open Trace

/-- Reuse the complete native path/history engine with imported clock laws. -/
instance nativeClockLaws [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
  finalBound _ row h := final_clock_bound h
  advance hp inverse _ row h bound := by
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
    obtain ⟨carry, bit, low, high⟩ := timestamp_equations inverse core
    have final := final_clock_bound h
    apply Trace.Proofs.increment hp bound final bit
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using low
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using high
  portsClocks _ := memory_clocks
  offsets _ := rfl
  effects hp inverse _ _ h inputs := clocks hp inverse h inputs

/-- Both output PC limbs are ranged by imported queries, including the
    terminal boundary. No terminal normalization premise is needed here. -/
theorem outgoing_pc_bounds {p : Nat} [Fact p.Prime]
    {trace : NativeTrace p} (accepted : Accepted trace) :
    ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  intro row member
  have h := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have ranges := local_ranges h
  exact ranges

end Airbender.ShiftBinop.Proofs
