import Clean.Specs.Keccak256

set_option Elab.async false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Tests.KeccakKnownAnswer

/-- XKCP's all-zero Keccak-f[1600] input after 24 rounds. The published rows
vary x first; this vector is transposed to Clean's lane index 5*x+y.
https://github.com/XKCP/XKCP/blob/4affab454735d54e78156880b3b44e38dcbf765c/tests/TestVectors/KeccakF-1600-IntermediateValues.txt
Source SHA-256: db0947545a5d91c20b2105aac75fac430deafe0ccaecb660af60044244df30d4.
This checks the reference permutation, not split/special5 circuit coverage. -/
theorem zero_permutation :
    Specs.Keccak256.keccakPermutation (Vector.replicate 25 0) =
      #v[0xf1258f7940e1dde7, 0xff97a42d7f8e6fd4, 0xeb5aa93f2317d635,
        0x05e5635a21d9ae61, 0x940c7922ae3a2614,
        0x84d5ccf933c0478a, 0x90fee5a0a44647c4, 0xa9a6e6260d712103,
        0x64befef28cc970f2, 0x1841f924a2c509e4,
        0xd598261ea65aa9ee, 0x8c5bda0cd6192e76, 0x81a57c16dbcf555f,
        0x613670957bc46611, 0x16f53526e70465c2,
        0xbd1547306f80494d, 0xad30a6f71b19059c, 0x43b831cd0347c826,
        0xb87c5a554fd00ecb, 0x75f644e97f30a13b,
        0x8b284e056253d057, 0x30935ab7d08ffc64, 0x01f22f1a11a5569f,
        0x8c3ee88a1ccf32c8, 0xeaf1ff7b5ceca249] := by
  decide +kernel

/-- NIST's FIPS 202 SHA3-256 example for an empty message supplies a second,
nonzero input to Keccak-f[1600]. The absorbed block has byte 0x06 in lane
(0, 0) and the final 0x80 bit in lane (1, 3). NIST prints lanes with x varying
first; the vectors below use Clean's index 5*x+y.
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA3-256_Msg0.pdf
Pages 2 and 37, "Xor'd state (as lanes of integers)" and "State (as lanes of
integers)". This checks the reference only, not either native Keccak path. -/
theorem fips202_sha3_256_empty_permutation :
    Specs.Keccak256.keccakPermutation
      #v[0x6, 0, 0, 0, 0,
        0, 0, 0, 0x8000000000000000, 0,
        0, 0, 0, 0, 0,
        0, 0, 0, 0, 0,
        0, 0, 0, 0, 0] =
      #v[0x66d71ebff8c6ffa7, 0xff875921cacc9566, 0xc287a923afe81e79,
        0x5375f6fb6aa989b0, 0x33fc34664d479817,
        0x62d661a05647c151, 0x80d97b5776b3ba89, 0x21684ae301601f33,
        0xc2c6b96032faf11e, 0x2b715c1a078fde58,
        0xfa493be44dff80f5, 0x28debd55fc6a313b, 0x282e7e469e09e75f,
        0x63684dd3f055a1b2, 0x140b7c9251369779,
        0x4a43f8804b0ad882, 0x03ac3d19f1e48ecc, 0xd17d1ed2c282b6b8,
        0xd908398b988ec2b2, 0x857343a7aabdeb5e,
        0xe2f36b34b7be6652, 0x78193aecc1e434e9, 0xf050e0d2adaf434e,
        0x913f10903e0bd326, 0x92136e0efb7b70e5] := by
  decide +kernel

end Tests.KeccakKnownAnswer
