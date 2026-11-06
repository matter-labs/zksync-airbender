import Airbender.Review.Circuits.ReducedMachine.NativeArtifact

namespace Airbender.ReducedMachine.NativeClockProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4,#v[0,1],#v[13,14],#v[2,3],#v[15,16],
      #[⟨0,#v[132,133],134⟩,⟨1,#v[135,136],137⟩,⟨2,#v[138,139],140⟩]⟩ : Trace.TraceColumns) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts,importedConstraintsTraceColumns]

theorem memory_offsets : importedConstraintsMemoryPorts.toList.map
    (fun port => port.clock.offset) = [0,1,2] := rfl

end Airbender.ReducedMachine.NativeClockProofs
