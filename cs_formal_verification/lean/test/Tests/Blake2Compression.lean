import Slop.Blake2Round.Compression

namespace Tests.Blake2Compression
open Airbender Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def emptyState : Blake2Round.Compression.State :=
  (Blake2Round.Preparation.configuredIV,
    (Blake2Round.Preparation.configuredIV ++ Blake2Round.Preparation.iv).set 14
      (Blake2Round.Preparation.splitWord (Specs.BLAKE3.iv[6] ^^^ 0xffffffff)))

theorem empty_block_digest :
    (Blake2Round.Compression.run 0 emptyState (Vector.replicate 16 ⟨0, 0⟩)).1.map Word.value =
      #v[0x307a2169, 0x94809079, 0xd02111e1, 0x7c4a3542,
        0x48b6551f, 0x1ea5a12c, 0xfd0d251b, 0xf9eed01e] := by
  decide +kernel

end Tests.Blake2Compression
