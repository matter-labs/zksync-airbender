import Airbender.Proofs.Blake2Round.NativeCombinedKeyData

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup CombinedKeyData
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem combined_key0_shape : xor4x3Data.columns[0] =
      Column.mk #[.periodic 16 1 (Array.replicate 1024 0)] := rfl
theorem combined_key1_shape : xor4x3Data.columns[1] =
      Column.mk #[.periodic 16 0 secondTemplate] := rfl
theorem combined_key2_shape : xor4x3Data.columns[2] =
      Column.mk #[.periodic 128 0 thirdTemplate] := rfl
theorem combined_key3_shape : xor4x3Data.columns[3] =
      Column.mk #[.periodic 2048 0 (Array.range 8)] := rfl

end Airbender.Blake2Round.Proofs
