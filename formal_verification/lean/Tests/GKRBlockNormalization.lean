import Airbender.Proofs.GKRProtocol.BlockNormalization

namespace Tests.GKRBlockNormalization
open Airbender Airbender.Compiler
set_option warningAsError true

theorem rejects_affine_gap :
    mergeSetupBlocks (.affine 3 100 1) (.affine 5 104 1) = none := by decide +kernel

theorem rejects_changed_stride :
    mergeSetupBlocks (.affine 3 100 1) (.affine 5 103 2) = none := by decide +kernel

theorem rejects_nonzero_periodic_stride :
    mergeSetupBlocks (.periodic 2 1 #[0, 1]) (.periodic 2 1 #[0, 1]) = none := by decide +kernel

theorem nonzero_periodic_merge_would_change_rows :
    Setup.getFromBlocks [.periodic 4 1 #[0, 1]] 4 ≠
      Setup.getFromBlocks [.periodic 2 1 #[0, 1], .periodic 2 1 #[0, 1]] 4 := by decide +kernel

end Tests.GKRBlockNormalization
