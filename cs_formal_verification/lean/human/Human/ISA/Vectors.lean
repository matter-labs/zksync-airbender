module
public import Human.ISA.DelegationRuns

@[expose] public section

/-! # The standards' test vectors

The transcriptions of standards in `human/` give the standards' published answers on their own test inputs:
Blake2s (`Human/ISA/Blake2s.lean`, `compressRounds` in `Human/ISA/DelegationRuns.lean`) on RFC 7693's example,
Keccak-f[1600] (`Human/ISA/Keccak.lean`) on the zero state; and the Keccak delegations' slot map (`laneSlot`,
`Human/ISA/Delegations.lean`) matches Airbender's table. These pin how the spec reads Clean's natural-number
definitions as words and lanes. Proven by evaluation in the kernel: `RV.standard_vectors`. -/

namespace RV
open Spec

/-- RFC 7693, Appendix B: BLAKE2s-256("abc") = `508c5e8c 327c14e2 e1a72ba3 4eeb452f 37458b20 9ed63a29 4d999b4c
86675982` (digest bytes; here as little-endian words): one compression of the padded block, 10 rounds, counter 3,
last block. -/
def Blake2sTestVector : Prop :=
  (compressRounds 10 (Vector.ofFn configuredIV) #v[0x00636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3#32 true)
    = #v[0x8C5E8C50, 0xE2147C32, 0xA32BA7E1, 0x2F45EB4E, 0x208B4537, 0x293AD69E, 0x4C9B994D, 0x82596786]

/-- Keccak-f[1600] on the all-zero state: all 25 lanes of the Keccak team's
`KeccakF-1600-IntermediateValues.txt` result, in lane order. -/
def KeccakTestVector : Prop :=
  keccakF (Vector.replicate 25 0) =
    #v[0xF1258F7940E1DDE7, 0x84D5CCF933C0478A, 0xD598261EA65AA9EE, 0xBD1547306F80494D, 0x8B284E056253D057,
       0xFF97A42D7F8E6FD4, 0x90FEE5A0A44647C4, 0x8C5BDA0CD6192E76, 0xAD30A6F71B19059C, 0x30935AB7D08FFC64,
       0xEB5AA93F2317D635, 0xA9A6E6260D712103, 0x81A57C16DBCF555F, 0x43B831CD0347C826, 0x01F22F1A11A5569F,
       0x05E5635A21D9AE61, 0x64BEFEF28CC970F2, 0x613670957BC46611, 0xB87C5A554FD00ECB, 0x8C3EE88A1CCF32C8,
       0x940C7922AE3A2614, 0x1841F924A2C509E4, 0x16F53526E70465C2, 0x75F644E97F30A13B, 0xEAF1FF7B5CECA249]

/-- The slot of each lane after one round is row 1 of Airbender's `KECCAK_F1600_PERMUTATIONS` table, and after 24
rounds every lane is back in its own slot (row 24). -/
def KeccakSlotTable : Prop :=
  (List.finRange 25).map (fun p => (Delegation.laneSlot 1 p).val) =
    [0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21] ∧
  ∀ p, Delegation.laneSlot 24 p = p

def StandardVectors : Prop := Blake2sTestVector ∧ KeccakTestVector ∧ KeccakSlotTable

end RV
