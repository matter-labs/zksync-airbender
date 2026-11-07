import Airbender.Proofs.Blake2Round.Compression

set_option Elab.async false

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

private def abcState : Blake2Round.Compression.State :=
  (emptyState.1, emptyState.2.set 12
    (Blake2Round.Preparation.splitWord (Specs.BLAKE3.iv[4] ^^^ 3)))

/-- RFC 7693 Appendix B's BLAKE2s-256("abc"), in little-endian 32-bit words.
https://www.rfc-editor.org/rfc/rfc7693.html#appendix-B
This exercises the project compression reference with t = 3 and f1 = 0;
it is a known-answer regression, not full RFC or circuit correspondence. -/
theorem rfc7693_abc_digest :
    (Blake2Round.Compression.run 0 abcState
      ((Vector.replicate 16 ⟨0, 0⟩).set 0 (Word.ofBitVec (BitVec.ofNat 32 0x00636261)))).1.map Word.value =
      #v[0x8c5e8c50, 0xe2147c32, 0xa32ba7e1, 0x2f45eb4e,
        0x208b4537, 0x293ad69e, 0x4c9b994d, 0x82596786] := by
  decide +kernel

end Tests.Blake2Compression
