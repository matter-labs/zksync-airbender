import Airbender.Review.UnifiedReduced.NativeROM
import Airbender.Review.Trace.Execution

namespace Airbender.UnifiedReduced
open Trace Reference.RiscV.Sail

/-- Public inputs shared by standard and combined standard/custom traces. `boot` binds
    initial cells, public instruction bytes, clocks and modeled tables. The
    remaining fields select Sail's ordinary Machine execution path and the
    supported instruction profile. Native history derives all row reads and
    word bounds; no instruction result is supplied here. -/
structure ExecutionInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  boot : BootInputsWith projection trace initial cells program
  /-- All architectural registers have public initialized cells, including x0. -/
  registers : ∀ index, Cell.register index ∈ cells
  /-- Fetch uses aligned instruction words within the public readonly ROM. -/
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  /-- Public CSR data selects the reviewed Sail memory path. -/
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  /-- Indirect-jump programs disable the experimental landing pad. -/
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd, entry.instruction = .JALR (imm, rs1, rd)) → ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  /-- Native LW-to-x0 is a project NOP; this claim uses unchanged Sail instead. -/
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

/-- The standard registry instantiates the shared public execution conditions. -/
abbrev ExecutionInputs {p : Nat} [Fact p.Prime] := ExecutionInputsWith (p := p) decoderFields

/-- Actual fetch, original Sail decoding and retirement for one unified row. -/
abbrev Step [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :=
  StepWith decoderFields instructionClause

end Airbender.UnifiedReduced
