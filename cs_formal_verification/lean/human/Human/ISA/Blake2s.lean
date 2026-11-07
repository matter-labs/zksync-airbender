import Human.ISA.State
import Mathlib.Data.Fin.VecNotation
import Clean.Specs.BLAKE3

/-! # The Blake2s building blocks (RFC 7693): constants, `G`, one round, used by Airbender's Blake2s delegations
(`Delegations`). The external reference is Clean's `Specs.BLAKE3` (pinned in `lakefile.toml`): BLAKE3 shares
Blake2s's `IV`, `G` (rotations 16, 12, 8, 7) and column/diagonal round, on natural-number words; it has no `SIGMA`
(its message schedule is a fixed permutation), so a Blake2s round is Clean's round on the `SIGMA`-permuted block. -/

namespace Spec
open RV (Word)

/-- The initialisation vector: Clean's `iv`. -/
def IV (i : Fin 8) : Word := BitVec.ofNat 32 (Specs.BLAKE3.iv[i]).toNat

/-- The message schedule of the 10 rounds. -/
def SIGMA : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    ![11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    ![7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    ![9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    ![2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    ![12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    ![13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    ![6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    ![10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- The initial state of an unkeyed Blake2s with a 32-byte digest: `IV`, parameter word `0x01010020` in word 0. -/
def configuredIV : Fin 8 → Word := fun i => IV i ^^^ (if i = 0 then 0x01010020#32 else 0#32)

/-- The mixing function `G` on words `a b c d` of the working vector, with message words `x y`: Clean's `g`. -/
def G (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) : Vector Word 16 :=
  (Specs.BLAKE3.g (v.map BitVec.toNat) a b c d x.toNat y.toNat).map (BitVec.ofNat 32)

/-- One round: `G` on the four columns, then on the four diagonals, message words in schedule `s`: Clean's `round`
on the block permuted by `s`. -/
def round (m : Vector Word 16) (s : Fin 16 → Fin 16) (v : Vector Word 16) : Vector Word 16 :=
  (Specs.BLAKE3.round (v.map BitVec.toNat) (Vector.ofFn fun i => m[s i].toNat)).map (BitVec.ofNat 32)

end Spec
