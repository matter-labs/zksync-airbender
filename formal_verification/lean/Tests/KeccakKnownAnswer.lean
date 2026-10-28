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

end Tests.KeccakKnownAnswer
