import Airbender.Review.Helpers.Context.InitializationUnifiedInputs
import Airbender.Proofs.Initialization.Boundary

namespace Airbender.Initialization.Proofs
open Trace
set_option warningAsError true
set_option Elab.async false
variable {p : Nat} [Fact p.Prime] [CommRing E]

theorem unified_inputs {base : UnifiedTrace p} {layout : Layout}
    {geometry : Geometry layout} {windows : Windows layout}
    (embed : ZMod p →+* E) (additive : E) (weights : Fin 6 → E)
    (raw : Raw p) (terminalRegisters : List (MemoryToken p))
    {initial : Reference.RiscV.Sail.State} {program : List UnifiedReduced.ProgramEntry}
    (profile : UnifiedProfile base layout geometry windows initial program) :
    UnifiedReduced.ExecutionInputs
      (withBoundary base layout (parametersFor embed additive weights windows) raw terminalRegisters)
      initial (cells geometry windows) program := by
  exact {
    boot := {
      distinct := ExternalBoundary.Initialization.Proofs.cells_distinct (windows.selection geometry)
      aligned := ExternalBoundary.Initialization.Proofs.aligned (windows.selection geometry)
      profile := profile.profile
      image := profile.image
      seed := computed_seed base layout geometry windows embed additive weights raw terminalRegisters
      initialPC := profile.initialPC
      programImage := profile.programImage
      setup := profile.setup }
    registers := ExternalBoundary.Initialization.Proofs.all_registers (windows.selection geometry)
    code := profile.code
    configuration := profile.configuration
    ordinary := profile.ordinary
    landingPadDisabled := profile.landingPadDisabled
    loads := profile.loads }

end Airbender.Initialization.Proofs
