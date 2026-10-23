import Airbender.Review.Helpers.UnifiedReduced.PathPreparation
import Airbender.Review.Helpers.UnifiedReduced.RegisterDataflow

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- One original instruction at an actual occurrence cut. Code coverage is
    syntactic; instruction effects and the absence of workers are derived. -/
structure PathInstructionPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat)
    (instruction : SailRV32.instruction) : Prop where
  code : ∀ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut →
    ∃ entry ∈ program, entry.pc = row.start.word.toBitVec ∧ entry.instruction = instruction
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Syntactic GPR frames. Branches may be taken or untaken, jumps keep their real
    link writes to another register, and stores keep their actual RAM writes. -/
inductive PathRegisterFrame (register : BitVec 5) : SailRV32.instruction → Prop where
  | write {instruction : SailRV32.instruction} {destination : BitVec 5}
      (form : PublicRegisterWrite instruction destination) (nonzero : destination ≠ 0)
      (different : destination ≠ register) : PathRegisterFrame register instruction
  | discarded {instruction : SailRV32.instruction}
      (form : ArithmeticRegisterWrite instruction 0) : PathRegisterFrame register instruction
  | load (immediate : BitVec 12) (source destination : BitVec 5)
      (different : destination ≠ register) :
      PathRegisterFrame register (.LOAD (immediate, .Regidx source, .Regidx destination, false, 4))
  | store (immediate : BitVec 12) (stored source : BitVec 5) :
      PathRegisterFrame register (.STORE (immediate, .Regidx stored, .Regidx source, 4))
  | branch (immediate : BitVec 13) (right left : BitVec 5) (operation : SailRV32.bop) :
      PathRegisterFrame register (.BTYPE (immediate, .Regidx right, .Regidx left, operation))
  | jal (immediate : BitVec 21) (destination : BitVec 5) (different : destination ≠ register) :
      PathRegisterFrame register (.JAL (immediate, .Regidx destination))
  | jalr (immediate : BitVec 12) (source destination : BitVec 5)
      (different : destination ≠ register) :
      PathRegisterFrame register (.JALR (immediate, .Regidx source, .Regidx destination))

/-- A finite public register computation along the actual occurrence path.
    Its value comes from encoded literals, actual public AUIPC placement and
    dependent ADDIs. Intervening frames constrain only the syntactic destination;
    actual reads, refreshed token times and other writes remain conclusions. -/
inductive PathRegisterDataflow [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Nat → BitVec 5 → BitVec 32 → Prop where
  | literal {cut register literal}
      (scope : PathPreparation data program cut register (.literal literal)) :
      PathRegisterDataflow data program cut register literal.value
  | auipc {cut register immediate pc}
      (scope : PathPreparation data program cut register (.auipc immediate))
      (placement : ∀ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut →
        ∀ entry ∈ program, entry.pc = row.start.word.toBitVec →
          entry.instruction = (.auipc immediate : PathWrite).instruction register → entry.pc = pc) :
      PathRegisterDataflow data program cut register (pc + (immediate ++ (0 : BitVec 12)))
  | addi {cut source register value immediate}
      (prior : PathRegisterDataflow data program (cut - 4) source value)
      (scope : PathInstructionPreparation data program cut
        (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI)))
      (sourceNonzero : source ≠ 0) :
      PathRegisterDataflow data program cut register (registerImmediateValue value immediate)
  | frame {cut register value instruction}
      (prior : PathRegisterDataflow data program (cut - 4) register value)
      (scope : PathInstructionPreparation data program cut instruction)
      (form : PathRegisterFrame register instruction) :
      PathRegisterDataflow data program cut register value

end Airbender.UnifiedReduced.Caller
