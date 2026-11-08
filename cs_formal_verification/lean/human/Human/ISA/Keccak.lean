import Mathlib.Data.Fin.VecNotation
import CleanCore.Specs.Keccak256

/-! # Keccak-f[1600] (FIPS 202, §3.2): 25 lanes of 64 bits, lane `(x, y)` at index `x + 5y`. The permutation is
Clean's `keccakPermutation` (pinned in `lakefile.toml`; transcribed as `Airbender.Specs.Keccak256.keccakPermutation` in
CleanCore), which numbers lanes `5x + y`. The pieces
below are the maps Airbender's Keccak delegations (`Delegations`) apply one call at a time; `DelegationRuns` states
that their runs compute `keccakF`. -/

namespace Spec

abbrev Lane := BitVec 64

/-- The lane index of `(x, y)`. -/
def lane (x y : Fin 5) : Fin 25 := ⟨x.val + 5 * y.val, by omega⟩
def laneX (p : Fin 25) : Fin 5 := ⟨p.val % 5, by omega⟩
def laneY (p : Fin 25) : Fin 5 := ⟨p.val / 5, by omega⟩

/-- The ρ offsets `r[x][y]`. -/
def rhoOffset : Fin 5 → Fin 5 → Nat :=
  ![![0, 36, 3, 41, 18], ![1, 44, 10, 45, 2], ![62, 6, 43, 15, 61], ![28, 55, 25, 21, 56], ![27, 20, 39, 8, 14]]

/-- The round constants: Clean's `roundConstants`. -/
def RC (r : Fin 24) : Lane := BitVec.ofNat 64 (Airbender.Specs.Keccak256.roundConstants[r]).toNat

/-- θ's `D[x] = C[x - 1] ⊕ rot(C[x + 1], 1)` from the column parities. -/
def thetaD (C : Fin 5 → Lane) (x : Fin 5) : Lane := C (x - 1) ^^^ (C (x + 1)).rotateLeft 1

/-- π moves lane `(x, y)` to `(y, 2x + 3y)`: the lane now at `(x', y')` came from `(x' + 3y', x')`. -/
def piSrc (p : Fin 25) : Fin 25 := lane (laneX p + 3 * laneY p) (laneX p)

/-- Clean's lane index `5x + y` of our lane `x + 5y` (and back: the map is its own inverse). -/
def cleanLane (p : Fin 25) : Fin 25 := ⟨5 * (p.val % 5) + p.val / 5, by omega⟩

/-- Keccak-f[1600]: Clean's `keccakPermutation`, with lanes renumbered. -/
def keccakF (A : Vector Lane 25) : Vector Lane 25 :=
  let out := Airbender.Specs.Keccak256.keccakPermutation (Vector.ofFn fun c => A[cleanLane c].toNat)
  Vector.ofFn fun p => BitVec.ofNat 64 out[cleanLane p]

end Spec
