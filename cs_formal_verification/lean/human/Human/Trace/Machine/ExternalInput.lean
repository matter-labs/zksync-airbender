module
public import Human.Helpers.Decoder.PooledExternalInput
public import Human.Circuits.UnifiedReduced.Delegation
public import Human.Helpers.Memory.Values

@[expose] public section
namespace Airbender.Trace.Machine

/-- The unified external-read selector comes from the imported native decoder placement. -/
def unifiedIsRead [Fact p.Prime] (row : Trace.Row p UnifiedFamily) : Bool :=
  row.assignment UnifiedReduced.importedConstraintsDecoderColumns.flags[8] == 1

/-- The unified external response is the native destination write token's word. -/
def unifiedResponse [Fact p.Prime] (row : Trace.Row p UnifiedFamily) : BitVec 32 :=
  (UnifiedReduced.Caller.destinationToken row.assignment).word.toBitVec

/-- Bind unified response ports, in native clock order, to an independent public input stream.
    This interface supplies stream values. It does not supply an ISA execution. -/
def UnifiedStreamPorts [Fact p.Prime] (trace : UnifiedTrace p) (stream : List (BitVec 32)) : Prop :=
  ExternalStream.Ports Trace.Row.clock unifiedIsRead unifiedResponse trace.rows stream

end Airbender.Trace.Machine
