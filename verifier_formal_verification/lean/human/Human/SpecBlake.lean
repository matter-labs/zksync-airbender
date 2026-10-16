import Human.Blake2s

/-! # What `blake2s_compress` should compute: one Blake2s compression (RFC 7693), reduced to 7 rounds

As the verifier's transcript uses it (`blake2s_u32`, `round_function_reduced_rounds`): 32-bit words, the byte
counter `t` (one word, inputs < 4 GB), `last` marks the final block. -/

namespace Spec
open RV (Word)

/-- The compression of the 16-word block `m` into the state `h`, the counter `t` already including this block. -/
def compress (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool) : Vector Word 8 :=
  let v₀ : Vector Word 16 := #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3,
    t ^^^ IV 4, IV 5, (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6, IV 7]
  let v := round m (SIGMA 6) <| round m (SIGMA 5) <| round m (SIGMA 4) <| round m (SIGMA 3) <|
    round m (SIGMA 2) <| round m (SIGMA 1) <| round m (SIGMA 0) v₀
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-- Blake2s with 7 rounds (no key, 32-byte digest) of the five words `w` (20 bytes, one block): the digest words. -/
def blake5 (w : Vector Word 5) : Vector Word 8 :=
  compress (Vector.ofFn fun i => IV i ^^^ (if i = 0 then 0x01010020#32 else 0#32))
    #v[w[0], w[1], w[2], w[3], w[4], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 20#32 true

end Spec
