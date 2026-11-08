import Human.Helpers.Context.Registries.SubwordMemory
import Slop.SubwordMemory.Timestamp
import Slop.Trace.RowHistory
import Slop.SubwordMemory

namespace Airbender.SubwordMemory

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := rfl

@[simp] theorem trace_decoder_columns (kind : TraceKind) :
    Trace.CircuitLayout.decoderColumns kind = importedConstraintsDecoderColumns := rfl

@[simp] theorem trace_constraints [Fact p.Prime] (kind : TraceKind)
    (rom : Table (ZMod p) (fields 9)) :
    Trace.CircuitLayout.constraints kind rom = clockConstraints rom := rfl

end Airbender.SubwordMemory

namespace Airbender.SubwordMemory.Proofs
open Trace

/-- Reuse the complete native path/history engine with imported clock laws. -/
instance nativeClockLaws [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
  finalBound _ row h := final_clock_bound h
  advance hp inverse setup row h bound := by
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
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

theorem outgoing_pc_bounds {p : Nat} [Fact p.Prime]
    {trace : NativeTrace p} (accepted : Accepted trace) :
    ∀ row ∈ trace.rows, row.finish.word.Bounded := by
  intro row member
  have core := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have ranges := local_ranges core
  exact ⟨ranges.2.2.2.1, ranges.2.2.2.2⟩

end Airbender.SubwordMemory.Proofs
