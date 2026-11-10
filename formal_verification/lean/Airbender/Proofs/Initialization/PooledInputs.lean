import Airbender.Review.Helpers.Context.InitializationInputs
import Airbender.Proofs.Initialization.Boundary
import Airbender.Proofs.BabyBear

namespace Airbender.Initialization.Proofs
open Trace
set_option warningAsError true
set_option Elab.async false
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [CommRing E]

theorem pooled_inputs {base : PooledTrace babyBearModulus} {layout : Layout}
    {geometry : Geometry layout} {windows : Windows layout}
    (embed : ZMod babyBearModulus →+* E) (additive : E) (weights : Fin 6 → E)
    (raw : Raw babyBearModulus) (terminalRegisters : List (MemoryToken babyBearModulus))
    {initial : Reference.RiscV.Sail.State} {program : List PooledProgramEntry}
    (profile : PooledProfile base layout geometry windows initial program) :
    PooledBootInputs
      (withBoundary base layout (parametersFor embed additive weights windows) raw terminalRegisters)
      initial (cells geometry windows) program := by
  exact {
    registers := ExternalBoundary.Initialization.Proofs.all_registers (windows.selection geometry)
    ordinary := profile.ordinary
    configuration := profile.configuration
    landingPadDisabled := profile.landingPadDisabled
    code := profile.code
    loads := profile.loads
    distinct := ExternalBoundary.Initialization.Proofs.cells_distinct (windows.selection geometry)
    aligned := ExternalBoundary.Initialization.Proofs.aligned (windows.selection geometry)
    programImage := profile.programImage
    profile := profile.profile
    seed := computed_seed base layout geometry windows embed additive weights raw terminalRegisters
    initialBoundary := profile.initialBoundary
    physicalImage := profile.physicalImage
    subwordSetup := profile.subwordSetup
    verifierBoundary := profile.verifierBoundary }

end Airbender.Initialization.Proofs
