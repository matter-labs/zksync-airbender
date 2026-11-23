module
public import Proven.Trace.Machine.UnifiedRun
public import Proven.Trace.Machine.Boot
public import Proven.Final.Circuits.InitsTeardowns.Theorems

@[expose] public section
namespace Airbender.Trace.Machine
open Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The unified native machine executes the public program, with modular operations and matched worker calls. -/
theorem unified : Unified := by
  intro trace workers initial cells program inits boot setup tables noSpecial stream accepted
  obtain ⟨addresses, programImage⟩ := boot.programImage
  have clocks := boot_clocks InitsTeardowns.unified_claim.1 boot
  exact unified_realizes accepted clocks.initial clocks.aligned boot.image boot.distinct boot.aligned
    programImage setup tables (boot_start boot) noSpecial stream

end Airbender.Trace.Machine
