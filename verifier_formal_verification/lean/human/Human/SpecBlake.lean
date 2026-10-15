import Human.RV32
import Mathlib.Data.Fin.VecNotation

/-! # What `blake2s_compress` should compute: one Blake2s compression (RFC 7693), reduced to 7 rounds

As the verifier's transcript uses it (`blake2s_u32`, `round_function_reduced_rounds`): 32-bit words, the byte
counter `t` (one word, inputs < 4 GB), `last` marks the final block. -/

namespace Spec
open RV (Word)

/-- The initialisation vector. -/
def IV : Fin 8 → Word :=
  ![0x6A09E667#32, 0xBB67AE85#32, 0x3C6EF372#32, 0xA54FF53A#32, 0x510E527F#32, 0x9B05688C#32, 0x1F83D9AB#32,
    0x5BE0CD19#32]

/-- The message schedule of the first 7 rounds. -/
def SIGMA : Fin 7 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    ![11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    ![7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    ![9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    ![2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    ![12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11]]

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

/-- The compression of the 16-word block `m` into the state `h`, the counter `t` already including this block. -/
def compress (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool) : Vector Word 8 :=
  let v₀ : Vector Word 16 := #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3,
    t ^^^ IV 4, IV 5, (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6, IV 7]
  let v := round m (SIGMA 6) <| round m (SIGMA 5) <| round m (SIGMA 4) <| round m (SIGMA 3) <|
    round m (SIGMA 2) <| round m (SIGMA 1) <| round m (SIGMA 0) v₀
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

end Spec
