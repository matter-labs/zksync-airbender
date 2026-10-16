import Human.State
import Mathlib.Data.Fin.VecNotation

/-! # The Blake2s building blocks (RFC 7693): constants, `G`, one round. Used by `SpecBlake` (what the program
should compute) and by Airbender's Blake2s delegation (`Delegations`). -/

namespace Spec
open RV (Word)

/-- The initialisation vector. -/
def IV : Fin 8 → Word :=
  ![0x6A09E667#32, 0xBB67AE85#32, 0x3C6EF372#32, 0xA54FF53A#32, 0x510E527F#32, 0x9B05688C#32, 0x1F83D9AB#32,
    0x5BE0CD19#32]

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

/-- The mixing function `G` on words `a b c d` of the working vector, with message words `x y`. -/
def G (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) : Vector Word 16 :=
  let a₁ := v[a] + v[b] + x
  let d₁ := (v[d] ^^^ a₁).rotateRight 16
  let c₁ := v[c] + d₁
  let b₁ := (v[b] ^^^ c₁).rotateRight 12
  let a₂ := a₁ + b₁ + y
  let d₂ := (d₁ ^^^ a₂).rotateRight 8
  let c₂ := c₁ + d₂
  let b₂ := (b₁ ^^^ c₂).rotateRight 7
  ((((v.set a a₂).set b b₂).set c c₂).set d d₂)

/-- One round: `G` on the four columns, then on the four diagonals. -/
def round (m : Vector Word 16) (s : Fin 16 → Fin 16) (v : Vector Word 16) : Vector Word 16 :=
  let v := G v 0 4 8 12 m[s 0] m[s 1]
  let v := G v 1 5 9 13 m[s 2] m[s 3]
  let v := G v 2 6 10 14 m[s 4] m[s 5]
  let v := G v 3 7 11 15 m[s 6] m[s 7]
  let v := G v 0 5 10 15 m[s 8] m[s 9]
  let v := G v 1 6 11 12 m[s 10] m[s 11]
  let v := G v 2 7 8 13 m[s 12] m[s 13]
  G v 3 4 9 14 m[s 14] m[s 15]

end Spec
