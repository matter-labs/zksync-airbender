import Airbender.Proofs.FullUnsigned.ParitySourceBinding
import Airbender.Proofs.FullUnsigned.ThetaSourceBinding
import Airbender.Proofs.FullUnsigned.ChiSourceBinding
import Airbender.Proofs.FullUnsigned.TaggedSetupInterpretation

namespace Airbender.Compiler.MachineTargets.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Native execution and initialization prove the complete full unsigned target. -/
theorem unrolled_full_soundness
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] : UnrolledFullUnsigned := by
  apply unrolled_full_soundness_of_guarded_source_rows
  · intro prime
    exact parity_original_source_rows
  · intro prime
    exact theta_original_source_rows
  · intro prime
    exact chi_original_source_rows

end Airbender.Compiler.MachineTargets.Proofs
