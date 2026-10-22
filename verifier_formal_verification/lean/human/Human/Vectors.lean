import Human.Delegations
import Human.SpecBlake

/-! # The standards' test vectors

The transcriptions of standards in `human/` give the standards' published answers on their own test inputs:
Blake2s (`Human/Blake2s.lean`) on RFC 7693's example, Keccak-f[1600] (`Human/Keccak.lean`) on the zero state; and
the Keccak delegations' slot map (`laneSlot`, `Human/Delegations.lean`) matches Airbender's table. Proven by
evaluation in the kernel: `RV.standard_vectors` (`slop/Slop/Deleg/Vectors.lean`). -/

namespace RV
open Spec

/-- RFC 7693, Appendix B: BLAKE2s-256("abc") = `508c5e8c 327c14e2 e1a72ba3 4eeb452f 37458b20 9ed63a29 4d999b4c
86675982` (digest bytes; here as little-endian words): one compression of the padded block, 10 rounds, counter 3,
last block. -/
def Blake2sTestVector : Prop :=
  (compressRounds 10 (Vector.ofFn configuredIV) #v[0x00636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3#32 true)
    = #v[0x8C5E8C50, 0xE2147C32, 0xA32BA7E1, 0x2F45EB4E, 0x208B4537, 0x293AD69E, 0x4C9B994D, 0x82596786]

/-- Keccak-f[1600] on the all-zero state: the first two lanes of the published result (the Keccak team's
`KeccakF-1600-IntermediateValues.txt`). -/
def KeccakTestVector : Prop :=
  (keccakF (Vector.replicate 25 0)).toList.take 2 = [0xF1258F7940E1DDE7, 0x84D5CCF933C0478A]

/-- The slot of each lane after one round is row 1 of Airbender's `KECCAK_F1600_PERMUTATIONS` table, and after 24
rounds every lane is back in its own slot (row 24). -/
def KeccakSlotTable : Prop :=
  (List.finRange 25).map (fun p => (Delegation.laneSlot 1 p).val) =
    [0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21] ∧
  ∀ p, Delegation.laneSlot 24 p = p

def StandardVectors : Prop := Blake2sTestVector ∧ KeccakTestVector ∧ KeccakSlotTable

end RV
