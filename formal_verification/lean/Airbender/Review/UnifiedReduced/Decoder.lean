import Airbender.Review.Trace.UnifiedReduced
import Airbender.Review.Trace.Program
import Airbender.Review.JumpBranchSlt.Decoder
import Airbender.Review.ShiftBinop.Decoder

namespace Airbender.UnifiedReduced

/-- Reuse arithmetic/LW/SW metadata. Unified LW/SW use bits 17/18;
    arithmetic keeps bits 0–2, including the existing x0 NOP preprocessing. -/
def arithmeticFields (data : Trace.DecoderData) : Trace.DecoderData Trace.UnifiedFamily :=
  { data.mapFamily (fun _ => .machine) with
    mask := match data.family with
      | .addSub => data.mask
      | .wordMemory => if data.mask = 0 then 131072 else 262144 }

/-- Jump/branch/comparison occupies bits 10–14 of the unified mask. -/
def jumpFields (data : Trace.DecoderData Unit) : Trace.DecoderData Trace.UnifiedFamily :=
  { data.mapFamily (fun _ => .machine) with mask := 1024 * data.mask }

/-- Shift/binop occupies bits 15–16. Binary queries use the pinned Rust
    WideXor/WideOr/WideAnd table IDs (52/53/54); shift tags are unchanged.
    This changes native lookup metadata, not instruction behavior. -/
def binaryFields (data : Trace.DecoderData Unit) : Trace.DecoderData Trace.UnifiedFamily :=
  { data.mapFamily (fun _ => .machine) with
    mask := 32768 * data.mask
    funct3 := if data.mask = 2 then
      if data.funct3 = 4 then 52 else if data.funct3 = 6 then 53 else 54
      else data.funct3 }

/-- Project actual Sail instructions using the already reviewed family
    metadata, then apply the unified Rust decoder's mask/tag remapping.
    Custom operations and discarded writes from other families are not admitted. -/
def decoderFields (instruction : SailRV32.instruction) :
    Option (Trace.DecoderData Trace.UnifiedFamily) :=
  (Trace.decoderFields instruction).map arithmeticFields <|>
  (JumpBranchSlt.decoderFields instruction).map jumpFields <|>
  (ShiftBinop.decoderFields instruction).map binaryFields

abbrev ProgramEntry := Trace.ProgramEntry Trace.UnifiedFamily

/-- The public program image is read from Sail memory and decoded by the
    pinned Sail decoder, including its configuration reads. Missing bytes,
    invalid encodings and unsupported operations make construction fail. -/
abbrev programImage := Trace.programImageRunWith decoderFields

abbrev decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :=
  Trace.decoderTable (p := p) program .machine

/-- All nine query fields, including the nineteen-bit mask, use the column
    descriptor imported from the unified JSON. -/
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- A fetched instruction comes from actual public Sail bytes and decoding.
    Query equality binds register indices, immediate, operation tag and mask;
    selector equations recover each bit. This supplies no desired memory read
    or instruction result. -/
def Fetched {p : Nat} (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State) : Prop :=
  ∃ entry : ProgramEntry, entry.SourceWith before decoderFields ∧
    decoderQuery w = entry.query ∧
    ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0

end Airbender.UnifiedReduced
