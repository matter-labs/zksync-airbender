import Airbender.Proofs.UnifiedReduced.PathDataflow
import Airbender.Review.Helpers.UnifiedReduced.RetirementProfile

namespace Tests.PathGapSyntax
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open Airbender.UnifiedReduced.Caller Airbender.UnifiedReduced.Caller.Proofs
set_option warningAsError true

/-- The common encoded NOP keeps its original Sail ADDI form. -/
example : SailRV32.Functions.encdec_backwards 0x00000013 =
    (_root_.Sail.ArchSem.FreeM.pure (.ITYPE (0, .Regidx 0, .Regidx 0, .ADDI)) : SailRV32.SailM _) := rfl

/-- Pure discarded arithmetic can frame every tracked register, including x0. -/
example (register rs2 rs1 : BitVec 5) :
    PathRegisterFrame register (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx 0, .ADD)) :=
  .discarded (.add rs2 rs1 0)

example (register rs2 rs1 : BitVec 5) :
    PathRegisterFrame register (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx 0, .SUB)) :=
  .discarded (.sub rs2 rs1 0)

example (register source : BitVec 5) (immediate : BitVec 12) :
    PathRegisterFrame register (.ITYPE (immediate, .Regidx source, .Regidx 0, .ADDI)) :=
  .discarded (.addi immediate source 0)

example (register : BitVec 5) (immediate : BitVec 20) :
    PathRegisterFrame register (.UTYPE (immediate, .Regidx 0, .LUI)) :=
  .discarded (.lui immediate 0)

example (register : BitVec 5) (immediate : BitVec 20) :
    PathRegisterFrame register (.UTYPE (immediate, .Regidx 0, .AUIPC)) :=
  .discarded (.auipc immediate 0)

/-- The discarded route derives the exact imported NOP decoder metadata. -/
example : UnifiedReduced.Mixed.decoderFields (.ITYPE (0, .Regidx 0, .Regidx 0, .ADDI)) =
    some ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ :=
  path_discarded_arithmetic_fields (.addi 0 0 0)

example (instruction : SailRV32.instruction) (form : ArithmeticRegisterWrite instruction 0) :
    UnifiedReduced.Mixed.decoderFields instruction = some ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ :=
  path_discarded_arithmetic_fields form

/-- A discarded LW is outside the pure arithmetic constructor. -/
example (immediate : BitVec 12) (source : BitVec 5) :
    ¬ ArithmeticRegisterWrite (.LOAD (immediate, .Regidx source, .Regidx 0, false, 4)) 0 := by
  intro form
  cases form

/-- The weaker native load frame remains available for an unrelated GPR. -/
example (immediate : BitVec 12) (source : BitVec 5) :
    PathRegisterFrame 10 (.LOAD (immediate, .Regidx source, .Regidx 0, false, 4)) :=
  .load immediate source 0 (by decide)

/-- Successful original execution still excludes that discarded load through
    the retained retirement profile, independently of the weaker native frame. -/
example [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [Fact p.Prime]
    (data : RequestTrace p) (before : State) (cells : List Cell)
    (entry : UnifiedReduced.ProgramEntry) (immediate : BitVec 12) (source : BitVec 5)
    (load : entry.instruction = .LOAD (immediate, .Regidx source, .Regidx 0, false, 4)) :
    ¬ RetirementProfile data [entry] before cells := by
  intro profile
  exact profile.loads entry (by simp) immediate source load

end Tests.PathGapSyntax
