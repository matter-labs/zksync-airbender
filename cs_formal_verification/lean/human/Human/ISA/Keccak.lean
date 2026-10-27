import Mathlib.Data.Fin.VecNotation

/-! # Keccak-f[1600] (FIPS 202, §3.2): 25 lanes of 64 bits, lane `(x, y)` at index `x + 5y`; a round is
`ι ∘ χ ∘ π ∘ ρ ∘ θ`; 24 rounds. Used by Airbender's Keccak delegations (`Delegations`). -/

namespace Spec

abbrev Lane := BitVec 64

/-- The lane index of `(x, y)`. -/
def lane (x y : Fin 5) : Fin 25 := ⟨x.val + 5 * y.val, by omega⟩
def laneX (p : Fin 25) : Fin 5 := ⟨p.val % 5, by omega⟩
def laneY (p : Fin 25) : Fin 5 := ⟨p.val / 5, by omega⟩

/-- The ρ offsets `r[x][y]`. -/
def rhoOffset : Fin 5 → Fin 5 → Nat :=
  ![![0, 36, 3, 41, 18], ![1, 44, 10, 45, 2], ![62, 6, 43, 15, 61], ![28, 55, 25, 21, 56], ![27, 20, 39, 8, 14]]

/-- The round constants. -/
def RC : Fin 24 → Lane :=
  ![0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000, 0x000000000000808b,
    0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008a, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000a, 0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The column parity `C[x]`. -/
def parity (A : Vector Lane 25) (x : Fin 5) : Lane :=
  A[lane x 0] ^^^ A[lane x 1] ^^^ A[lane x 2] ^^^ A[lane x 3] ^^^ A[lane x 4]

/-- θ's `D[x] = C[x - 1] ⊕ rot(C[x + 1], 1)` from the column parities. -/
def thetaD (C : Fin 5 → Lane) (x : Fin 5) : Lane := C (x - 1) ^^^ (C (x + 1)).rotateLeft 1

def theta (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p => A[p] ^^^ thetaD (parity A) (laneX p)
def rho (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p => A[p].rotateLeft (rhoOffset (laneX p) (laneY p))

/-- π moves lane `(x, y)` to `(y, 2x + 3y)`: the lane now at `(x', y')` came from `(x' + 3y', x')`. -/
def piSrc (p : Fin 25) : Fin 25 := lane (laneX p + 3 * laneY p) (laneX p)
def pi (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p => A[piSrc p]

def chi (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p =>
  A[p] ^^^ (~~~A[lane (laneX p + 1) (laneY p)] &&& A[lane (laneX p + 2) (laneY p)])
def iota (r : Fin 24) (A : Vector Lane 25) : Vector Lane 25 := A.set 0 (A[0] ^^^ RC r)

def keccakRound (r : Fin 24) (A : Vector Lane 25) : Vector Lane 25 := iota r (chi (pi (rho (theta A))))

/-- Keccak-f[1600]: the 24 rounds. -/
def keccakF (A : Vector Lane 25) : Vector Lane 25 := (List.finRange 24).foldl (fun A r => keccakRound r A) A

end Spec
