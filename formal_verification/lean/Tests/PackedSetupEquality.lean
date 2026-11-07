import Airbender.Proofs.GKRProtocol.PackedSetupEquality

namespace Tests.PackedSetupEquality
open Airbender.Setup Airbender.Compiler.PackedSetupEquality
set_option warningAsError true

theorem literal_bytes : (ArrayCode.literal 2 256).decode = #[0, 1] := by decide +kernel
theorem constant_array : (ArrayCode.constant 3 7).decode = #[7, 7, 7] := by decide +kernel
theorem range_array : (ArrayCode.range 3).decode = #[0, 1, 2] := by decide +kernel
theorem linear_array : (ArrayCode.linear 3 4).decode = #[4, 5, 6] := by decide +kernel
theorem rotated_array : (ArrayCode.rotate 3 2).decode = #[2, 0, 1] := by decide +kernel
theorem repeated_runs :
    (ArrayCode.linearRuns 4 1 2 2).decode = #[1, 1, 3, 3] := by decide +kernel
theorem indexed_runs :
    (ArrayCode.lookupRuns 4 2 (.literal 2 256)).decode = #[0, 0, 1, 1] := by decide +kernel
theorem adopted_byte_array : (ArrayCode.packedBytes 2 256).decode = #[0, 1] := by decide +kernel
theorem signed_stride :
    Airbender.Compiler.PackedSetupEquality.check [.periodic 3 (-2) (.literal 2 256)]
      [.periodic 3 (-2) (.literal 2 256)] = true := by decide +kernel
theorem changed_stride_rejected :
    Airbender.Compiler.PackedSetupEquality.check [.periodic 3 (-2) (.literal 2 256)]
      [.periodic 3 2 (.literal 2 256)] = false := by decide +kernel
theorem changed_byte_rejected :
    Airbender.Compiler.PackedSetupEquality.check [.dense (.literal 2 256)]
      [.dense (.literal 2 257)] = false := by decide +kernel

theorem row_count_checked :
    Airbender.Compiler.PackedSetupEquality.checkWithLengths [.affine 3 0 1]
      [.affine 3 0 1] [⟨0, 1, 3⟩] = true := by decide +kernel
theorem changed_row_count_rejected :
    Airbender.Compiler.PackedSetupEquality.checkWithLengths [.affine 3 0 1]
      [.affine 3 0 1] [⟨0, 1, 4⟩] = false := by decide +kernel

end Tests.PackedSetupEquality
