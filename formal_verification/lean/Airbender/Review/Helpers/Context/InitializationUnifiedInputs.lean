import Airbender.Review.Circuits.Initialization.Boundary
import Airbender.Review.Helpers.UnifiedReduced.ExecutionInputs

namespace Airbender.Initialization
open Trace Reference.RiscV.Sail
variable {p : Nat} [Fact p.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public unified execution conditions, with RAM boundary tokens computed by
    the imported inline slice. Uniqueness, alignment, register coverage and the
    zero native seed are derived from geometry and the selected windows. -/
structure UnifiedProfile (base : UnifiedTrace p) (layout : Layout)
    (geometry : Geometry layout) (windows : Windows layout)
    (initial : State) (program : List UnifiedReduced.ProgramEntry) : Prop where
  profile : InitialProfile initial (cells geometry windows)
  image : ∃ image : List (MemoryToken p), initialImage initial (cells geometry windows) = some image
  initialPC : base.initial = PCState.boundary 0 (4, 0)
  programImage : ∃ addresses,
    programImageRunWith UnifiedReduced.decoderFields initial addresses = some program
  setup : base.rom = UnifiedReduced.Setup.table initial
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells geometry windows → PlatformWordAddress address
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
    entry.instruction = .JALR (imm, rs1, rd)) → ∃ security,
    initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

end Airbender.Initialization
