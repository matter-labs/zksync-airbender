import Airbender.Review.Circuits.Initialization.Boundary
import Airbender.Review.Helpers.Context.PooledBoundary

namespace Airbender.Initialization
open Trace Reference.RiscV.Sail
variable {p : Nat} [Fact p.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public Sail/program/configuration inputs for the computed native boundary.
    Domain uniqueness/alignment and the native seed correspondence are derived,
    rather than supplied here. Register teardown is still a public boundary;
    these imported GKR slices compute RAM initialization and teardown only. -/
structure PooledProfile (base : PooledTrace p) (layout : Layout)
    (geometry : Geometry layout) (windows : Windows layout)
    (initial : State) (program : List PooledProgramEntry) : Prop where
  ordinary : ∀ address, Cell.ram address ∈ cells geometry windows → PlatformWordAddress address
  configuration : FlatMemoryConfiguration initial
  landingPadDisabled : ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  loads : NoDiscardedLoads program
  programImage : ∃ addresses, programImageRunWith pooledDecoderFields initial addresses = some program
  profile : InitialProfile initial (cells geometry windows)
  initialBoundary : base.initial = PCState.boundary 0 (4, 0)
  physicalImage : ∃ image, initialImage initial (cells geometry windows) = some image ∧
    base.rom.wordMemory = ROM.table (cells geometry windows) image
  subwordSetup : base.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  verifierBoundary : VerifierBoundary.BootClosure base.initial
    (base.rows.map Row.start) (base.rows.map Row.finish)

end Airbender.Initialization
