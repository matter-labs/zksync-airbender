module
public import Human.Helpers.Decoder.Program
public import Human.ISA.RV32
public import Human.Helpers.Decoder.RVProgram

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Decoder/RVProgram.lean` (no claim states them). -/

@[expose] public section
noncomputable section
namespace Airbender.Trace
open Arithmetic
/-- Change only the circuit registry tag. -/
def RVProgramEntry.mapFamily {Kind Target : Type} (f : Kind → Target)
    (entry : RVProgramEntry Kind) : RVProgramEntry Target :=
  ⟨entry.pc, entry.bits, entry.data.mapFamily f⟩
end Airbender.Trace
