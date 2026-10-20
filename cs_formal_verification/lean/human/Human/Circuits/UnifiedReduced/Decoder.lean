import Human.Helpers.UnifiedReduced.Registry
import Human.Helpers.Decoder.Program
import Human.Circuits.JumpBranchSlt.Decoder
import Human.Circuits.ShiftBinop.Decoder

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

/-- Native XORROT table IDs 47–50, from `definitions/table_type.rs`.
    The MOP number selects rotation 16/12/8/7; execution is the pinned
    Airbender operation, not upstream Zimop's zero-result fallback. -/
def customRotationTag (mop : BitVec 5) : Option Nat :=
  if mop = 16 then some 47 else if mop = 12 then some 48
  else if mop = 8 then some 49 else if mop = 7 then some 50 else none

/-- Project original Sail MOP decoding into the unified Rust metadata.
    TRIADD reads the old destination through its third port (bit 9).
    XORROT reads it as rs2 and uses the binary selector (bit 16).
    Unsupported MOP numbers and discarded x0 writes are excluded here;
    no instruction result or memory read is supplied. -/
def customDecoderFields : SailRV32.instruction →
    Option (Trace.DecoderData Trace.UnifiedFamily)
  | .ZIMOP_MOP_RR (mop, .Regidx rs2, .Regidx rs1, .Regidx rd) =>
    if mop = 4 ∧ rd ≠ 0 then some ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 512, 0⟩ else none
  | .ZIMOP_MOP_R (mop, .Regidx rs1, .Regidx rd) => do
    if rd = 0 then none else
      let tag ← customRotationTag mop
      some ⟨.machine, rs1, rd, rd, ⟨0, 0⟩, 65536, tag⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Trace.UnifiedFamily

/-- Public bytes run the original Sail Zimop decoder before custom metadata
    is projected. This constructs the custom fetch table; its instruction
    execution/trace claim is separate from the standard Sail claim. -/
abbrev customProgramImage := Trace.programImageRunWith customDecoderFields

/-- The public program image is read from Sail memory and decoded by the
    pinned Sail decoder, including its configuration reads. Missing bytes,
    invalid encodings and unsupported operations make construction fail. -/
abbrev programImage := Trace.programImageRunWith decoderFields

abbrev decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :=
  Trace.decoderTable (p := p) program .machine

/-- Every row's native query belongs to the program table. `programImage`
    separately binds these entries to public bytes and actual Sail decoding;
    this membership remains a logical lookup boundary. -/
def Decoded [Fact p.Prime] (trace : Trace.UnifiedTrace p) (program : List ProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (decoderTable program).Contains #[] row.decoderQuery

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
