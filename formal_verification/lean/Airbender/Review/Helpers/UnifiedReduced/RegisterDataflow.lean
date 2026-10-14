import Airbender.Review.Helpers.UnifiedReduced.RegisterChains

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Original arithmetic forms with their syntactic destination. Public Sail
    decoding, rather than a witness selector or desired output, binds the form. -/
inductive ArithmeticRegisterWrite : SailRV32.instruction → BitVec 5 → Prop where
  | add (rs2 rs1 rd : BitVec 5) : ArithmeticRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) rd
  | sub (rs2 rs1 rd : BitVec 5) : ArithmeticRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB)) rd
  | addi (imm : BitVec 12) (rs1 rd : BitVec 5) : ArithmeticRegisterWrite (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) rd
  | lui (imm : BitVec 20) (rd : BitVec 5) : ArithmeticRegisterWrite (.UTYPE (imm, .Regidx rd, .LUI)) rd
  | auipc (imm : BitVec 20) (rd : BitVec 5) : ArithmeticRegisterWrite (.UTYPE (imm, .Regidx rd, .AUIPC)) rd

/-- A public arithmetic gap. Its actual reads, values and timestamps remain
    unrestricted. Only this selected cycle is worker-free. -/
structure ArithmeticFramePreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (destination : BitVec 5) : Prop where
  registry : WrappedSequentialProgram program
  atCut : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
    ArithmeticRegisterWrite entry.instruction destination
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Retain the original ADDI entry as a special case of arithmetic gaps. -/
def RegisterImmediatePreparation.arithmeticFrame [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cut : Nat} {source destination : BitVec 5} {immediate : BitVec 12}
    (scope : RegisterImmediatePreparation data program cut source destination immediate) :
    ArithmeticFramePreparation data program cut destination :=
  ⟨scope.registry, by intro entry present address; rw [scope.atCut entry present address]; exact .addi _ _ _,
    scope.prefixScope, scope.afterInitial, scope.beforeTerminal⟩

/-- Public register dataflow with intervening arithmetic writes to other nonzero GPRs.
    Such a gap may read and refresh the tracked register; its value is preserved.
    Actual operands, tokens, selectors and intermediate states are conclusions.
    Each selected cycle is worker-free; all earlier effects remain. -/
inductive PublicRegisterDataflow [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Nat → BitVec 5 → BitVec 32 → Prop where
  | prepared {cut register value}
      (preparation : PublicRegisterPreparation data program cut register value) :
      PublicRegisterDataflow data program cut register value
  | addi {cut source register value immediate}
      (prior : PublicRegisterDataflow data program (cut - 4) source value)
      (scope : RegisterImmediatePreparation data program cut source register immediate)
      (nonzero : source ≠ 0) :
      PublicRegisterDataflow data program cut register (registerImmediateValue value immediate)
  | frame {cut register value source destination immediate}
      (prior : PublicRegisterDataflow data program (cut - 4) register value)
      (scope : RegisterImmediatePreparation data program cut source destination immediate)
      (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register) :
      PublicRegisterDataflow data program cut register value
  | arithmeticFrame {cut register value destination}
      (prior : PublicRegisterDataflow data program (cut - 4) register value)
      (scope : ArithmeticFramePreparation data program cut destination)
      (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register) :
      PublicRegisterDataflow data program cut register value

end Airbender.UnifiedReduced.Caller
