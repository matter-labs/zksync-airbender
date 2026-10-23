import Human.Helpers.Decoder.PooledProgram
import Human.Helpers.Decoder.ExternalInput

namespace Airbender.Trace.NonDeterminism.Pooled

variable {p : Nat} [Fact p.Prime]

/-- Extend the six-family metadata registry with the pinned project's custom
    CSR forms, reusing the existing projection. Instruction decoding still
    comes from Sail; this projection selects native columns and selectors. -/
def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData PooledFamily) :=
  (NonDeterminism.decoderFields instruction).map (DecoderData.mapFamily pooledArithmeticFamily) <|>
    pooledDecoderFields instruction

/-- Read public instruction bytes and invoke actual pinned Sail decoding,
    retaining the original constructor and pooled/custom metadata. -/
noncomputable abbrev programImage := programImageWith decoderFields

/-- The imported ADD/SUB external-read selector. Other pooled families never
    consume input, even when the same numeric column contains one.
    The decoder theorem binds it to the actual custom CSR read form. -/
def isRead (row : Row p PooledFamily) : Bool :=
  match row.family with
  | .addSub => NonDeterminism.isRead ⟨.addSub, row.assignment⟩
  | _ => false

/-- The external response in ADD/SUB's destination columns. It is used only
    for selected reads; the caller fixes the independent input stream. -/
def response (row : Row p PooledFamily) : BitVec 32 :=
  NonDeterminism.response ⟨.addSub, row.assignment⟩

/-- Count earlier external reads by native clock across the entire pool. -/
def readIndex (trace : PooledTrace p) (row : Row p PooledFamily) : Nat :=
  ExternalStream.index Row.clock isRead trace.rows row

/-- Total external-read count; all standard pooled rows consume zero words. -/
def readCount (trace : PooledTrace p) : Nat := ExternalStream.count isRead trace.rows

/-- Bind response ports to the independent stream using the shared clock-based
    interpretation. This supplies input values, not successful ISA execution. -/
def StreamPorts (trace : PooledTrace p) (stream : List (BitVec 32)) : Prop :=
  ExternalStream.Ports Row.clock isRead response trace.rows stream

/-- Responses in the chronological order derived from native matching. -/
def consumed (rows : List (Row p PooledFamily)) : List (BitVec 32) :=
  ExternalStream.consumed isRead response rows

/-- Fetch evidence proved from public image construction and decoder membership:
    an original Sail instruction at the native PC has matching family/query,
    and its custom-read classification agrees with the imported selector.
    This is a conclusion of the decoder theorem, not an execution assumption. -/
def Fetched (row : Row p PooledFamily) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : PooledProgramEntry, entry.SourceWith before decoderFields ∧
    entry.data.family = row.family ∧ row.decoderQuery = entry.query ∧
    row.start.word.toBitVec = entry.pc ∧ isRead row = NonDeterminism.instructionRead entry.instruction


end Airbender.Trace.NonDeterminism.Pooled
