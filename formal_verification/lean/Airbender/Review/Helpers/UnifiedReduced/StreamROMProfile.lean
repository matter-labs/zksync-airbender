import Airbender.Review.Helpers.UnifiedReduced.RetirementProfile

namespace Airbender.UnifiedReduced.Caller.Stream
open Trace Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public execution conditions for ROM-aware native histories.
Tracked cells can include readonly ROM shadows. Native equations and the
worker-domain proof must establish code preservation separately. -/
structure ROMProfile [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (initial : State) (cells : List Cell) : Prop where
  ordinaryCode : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  callerCode : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  registers : ∀ index, Cell.register index ∈ cells
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
    entry.instruction = .JALR (imm, rs1, rd)) →
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

end Airbender.UnifiedReduced.Caller.Stream
