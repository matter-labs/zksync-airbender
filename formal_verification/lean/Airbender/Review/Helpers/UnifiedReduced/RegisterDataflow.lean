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

/-- Public bitwise/shift forms and their syntactic destination. Actual public
    decoding still rejects discarded destinations and illegal RV32 shift payloads. -/
inductive BinaryRegisterWrite : SailRV32.instruction → BitVec 5 → Prop where
  | xor (rs2 rs1 rd : BitVec 5) : BinaryRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR)) rd
  | or (rs2 rs1 rd : BitVec 5) : BinaryRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)) rd
  | and (rs2 rs1 rd : BitVec 5) : BinaryRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)) rd
  | sll (rs2 rs1 rd : BitVec 5) : BinaryRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLL)) rd
  | srl (rs2 rs1 rd : BitVec 5) : BinaryRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRL)) rd
  | sra (rs2 rs1 rd : BitVec 5) : BinaryRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRA)) rd
  | xori (imm : BitVec 12) (rs1 rd : BitVec 5) : BinaryRegisterWrite (.ITYPE (imm, .Regidx rs1, .Regidx rd, .XORI)) rd
  | ori (imm : BitVec 12) (rs1 rd : BitVec 5) : BinaryRegisterWrite (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI)) rd
  | andi (imm : BitVec 12) (rs1 rd : BitVec 5) : BinaryRegisterWrite (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI)) rd
  | slli (amount : BitVec 6) (rs1 rd : BitVec 5) : BinaryRegisterWrite (.SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SLLI)) rd
  | srli (amount : BitVec 6) (rs1 rd : BitVec 5) : BinaryRegisterWrite (.SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SRLI)) rd
  | srai (amount : BitVec 6) (rs1 rd : BitVec 5) : BinaryRegisterWrite (.SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SRAI)) rd
  | rev8 (rs1 rd : BitVec 5) : BinaryRegisterWrite (.REV8 (.Regidx rs1, .Regidx rd)) rd

/-- The four original comparisons, with the public syntactic destination.
    Their actual operands and Boolean result are unrestricted here. -/
inductive ComparisonRegisterWrite : SailRV32.instruction → BitVec 5 → Prop where
  | slt (rs2 rs1 rd : BitVec 5) : ComparisonRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT)) rd
  | sltu (rs2 rs1 rd : BitVec 5) : ComparisonRegisterWrite (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU)) rd
  | slti (imm : BitVec 12) (rs1 rd : BitVec 5) : ComparisonRegisterWrite (.ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI)) rd
  | sltiu (imm : BitVec 12) (rs1 rd : BitVec 5) : ComparisonRegisterWrite (.ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU)) rd

/-- The pinned project's TRIADD and four XORROT forms. This footprint does not
    substitute upstream Zimop fallback execution or assert custom retirement. -/
inductive CustomRegisterWrite : SailRV32.instruction → BitVec 5 → Prop where
  | triadd (rs2 rs1 rd : BitVec 5) : CustomRegisterWrite (.ZIMOP_MOP_RR (4, .Regidx rs2, .Regidx rs1, .Regidx rd)) rd
  | xorrot16 (rs1 rd : BitVec 5) : CustomRegisterWrite (.ZIMOP_MOP_R (16, .Regidx rs1, .Regidx rd)) rd
  | xorrot12 (rs1 rd : BitVec 5) : CustomRegisterWrite (.ZIMOP_MOP_R (12, .Regidx rs1, .Regidx rd)) rd
  | xorrot8 (rs1 rd : BitVec 5) : CustomRegisterWrite (.ZIMOP_MOP_R (8, .Regidx rs1, .Regidx rd)) rd
  | xorrot7 (rs1 rd : BitVec 5) : CustomRegisterWrite (.ZIMOP_MOP_R (7, .Regidx rs1, .Regidx rd)) rd

/-- Supported public GPR-writing forms. Their results are unrestricted here. -/
inductive PublicRegisterWrite : SailRV32.instruction → BitVec 5 → Prop where
  | arithmetic {instruction destination} (form : ArithmeticRegisterWrite instruction destination) :
      PublicRegisterWrite instruction destination
  | binary {instruction destination} (form : BinaryRegisterWrite instruction destination) :
      PublicRegisterWrite instruction destination
  | comparison {instruction destination} (form : ComparisonRegisterWrite instruction destination) :
      PublicRegisterWrite instruction destination
  | custom {instruction destination} (form : CustomRegisterWrite instruction destination) :
      PublicRegisterWrite instruction destination

/-- One worker-free public GPR write, with no supplied operands or native flags. -/
structure RegisterFramePreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (destination : BitVec 5) : Prop where
  registry : WrappedSequentialProgram program
  atCut : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
    PublicRegisterWrite entry.instruction destination
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- A selected original LW. Discarded writes remain admitted as native NOPs;
    no successful original Sail load or expected loaded value is assumed. -/
structure LoadFramePreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat)
    (source destination : BitVec 5) (immediate : BitVec 12) : Prop where
  registry : WrappedSequentialProgram program
  atCut : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
    entry.instruction = .LOAD (immediate, .Regidx source, .Regidx destination, false, 4)
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- A selected original SW. Its effective address and actual write are derived;
    no RAM address, data value or empty transfer window is supplied. -/
structure StoreFramePreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat)
    (source stored : BitVec 5) (immediate : BitVec 12) : Prop where
  registry : WrappedSequentialProgram program
  atCut : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
    entry.instruction = .STORE (immediate, .Regidx stored, .Regidx source, 4)
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

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

/-- Arithmetic scopes retain their original public contract. -/
def ArithmeticFramePreparation.registerFrame [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cut : Nat} {destination : BitVec 5}
    (scope : ArithmeticFramePreparation data program cut destination) :
    RegisterFramePreparation data program cut destination :=
  ⟨scope.registry, fun entry present address => .arithmetic (scope.atCut entry present address),
    scope.prefixScope, scope.afterInitial, scope.beforeTerminal⟩

/-- Retain the original ADDI entry as a special case of arithmetic gaps. -/
def RegisterImmediatePreparation.arithmeticFrame [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cut : Nat} {source destination : BitVec 5} {immediate : BitVec 12}
    (scope : RegisterImmediatePreparation data program cut source destination immediate) :
    ArithmeticFramePreparation data program cut destination :=
  ⟨scope.registry, by intro entry present address; rw [scope.atCut entry present address]; exact .addi _ _ _,
    scope.prefixScope, scope.afterInitial, scope.beforeTerminal⟩

/-- Public register dataflow with intervening arithmetic, bitwise, shift, comparison
    and admitted custom writes to other nonzero GPRs, plus LW/SW memory gaps.
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

  | registerFrame {cut register value destination}
      (prior : PublicRegisterDataflow data program (cut - 4) register value)
      (scope : RegisterFramePreparation data program cut destination)
      (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register) :
      PublicRegisterDataflow data program cut register value

  | loadFrame {cut register value source destination immediate}
      (prior : PublicRegisterDataflow data program (cut - 4) register value)
      (scope : LoadFramePreparation data program cut source destination immediate)
      (preserves : destination ≠ register) :
      PublicRegisterDataflow data program cut register value
  | storeFrame {cut register value source stored immediate}
      (prior : PublicRegisterDataflow data program (cut - 4) register value)
      (scope : StoreFramePreparation data program cut source stored immediate) :
      PublicRegisterDataflow data program cut register value

end Airbender.UnifiedReduced.Caller
