import Airbender.Review.Helpers.UnifiedReduced.MixedFetch

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public execution profile for the existing ordinary registry in a shared
    caller/worker history. Reads, operands, native order and worker controls are
    derived separately; no valid-call condition is included. -/
structure RetirementProfile [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (initial : State) (cells : List Cell) : Prop where
  /-- Readonly aligned code and the existing tracked-RAM data domain. -/
  code : CodeProfile data program cells
  /-- Public initialization includes every architectural register. -/
  registers : ∀ index, Cell.register index ∈ cells
  /-- Machine configuration selects the reviewed Sail memory path. -/
  configuration : FlatMemoryConfiguration initial
  /-- Tracked data uses the existing ordinary aligned-word memory profile. -/
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  /-- Programs using JALR disable the experimental landing pad. -/
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
    entry.instruction = .JALR (imm, rs1, rd)) →
    ∃ security, initial.regs.get? .mseccfg = some security ∧
      SailRV32.Functions._get_Seccfg_MLPE security = 0
  /-- Preserve the unchanged-Sail restriction on discarded word loads. -/
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

end Airbender.UnifiedReduced.Caller
