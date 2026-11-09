module
public import CleanCore.Utils.Bitwise
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Init.Data.List.Find
public import Mathlib.Combinatorics.Enumerative.Composition

/-! # The BLAKE3 mixing function and round (Clean `Clean.Specs.BLAKE3`, pinned b41c196)

Clean's `iv`, `g`, `roundConstants` and `round`, transcribed verbatim. Blake2s shares the IV and the shape
of `G` and of a round (its rotation constants and message schedule are stated where it is used).
Deviation: BLAKE3's compression, chunking and flags are omitted. `CleanEquivalence` proves each
definition equal to Clean's. -/

@[expose] public section

namespace Airbender.Specs.BLAKE3

def iv : Vector UInt32 8 := #v[
  0x6a09e667,
  0xbb67ae85,
  0x3c6ef372,
  0xa54ff53a,
  0x510e527f,
  0x9b05688c,
  0x1f83d9ab,
  0x5be0cd19
]

def g (state : Vector ℕ 16) (a b c d : Fin 16) (mx my : ℕ) : Vector ℕ 16 :=
  let state_a := add32 (state[a]) (add32 state[b] mx)
  let state_d := rotRight32 (state[d] ^^^ state_a) 16
  let state_c := add32 (state[c]) state_d
  let state_b := rotRight32 (state[b] ^^^ state_c) 12

  let state_a := add32 state_a (add32 state_b my)
  let state_d := rotRight32 (state_d ^^^ state_a) 8
  let state_c := add32 state_c state_d
  let state_b := rotRight32 (state_b ^^^ state_c) 7

  state.set a state_a
        |>.set b state_b
        |>.set c state_c
        |>.set d state_d

/--
The constants a b c d for the G applications in the round, together with the indices
of the message words mx and my
-/
def roundConstants : Vector (Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16) 8 := #v[
  (0, 4, 8, 12, 0, 1),
  (1, 5, 9, 13, 2, 3),
  (2, 6, 10, 14, 4, 5),
  (3, 7, 11, 15, 6, 7),
  (0, 5, 10, 15, 8, 9),
  (1, 6, 11, 12, 10, 11),
  (2, 7, 8, 13, 12, 13),
  (3, 4, 9, 14, 14, 15)
]

/--
The round function, which applies the mixing function G
to mix the state's columns and diagonals.
-/
def round (state : Vector ℕ 16) (m : Vector ℕ 16) : Vector ℕ 16 :=
  roundConstants.foldl (fun state (a, b, c, d, i, j) =>
    g state a b c d m[i] m[j]
  ) state

end Airbender.Specs.BLAKE3
