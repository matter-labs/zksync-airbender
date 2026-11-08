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

/-- Native XORROT table IDs 47–50, from `definitions/table_type.rs`.
    The MOP number selects rotation 16/12/8/7; execution is the pinned
    Airbender operation, not upstream Zimop's zero-result fallback. -/
def customRotationTag (mop : BitVec 5) : Option Nat :=
  if mop = 16 then some 47 else if mop = 12 then some 48
  else if mop = 8 then some 49 else if mop = 7 then some 50 else none

/-- All nine query fields, including the nineteen-bit mask, use the column
    descriptor imported from the unified JSON. -/
abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

end Airbender.UnifiedReduced
