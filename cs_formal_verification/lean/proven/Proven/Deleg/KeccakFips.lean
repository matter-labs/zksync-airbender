module
public import Human.ISA.Keccak

@[expose] public section

/-! Keccak-f[1600] as FIPS 202 composes it (§3.2: a round is `ι ∘ χ ∘ π ∘ ρ ∘ θ`, 24 rounds) on our lane numbering
`x + 5y` and `BitVec 64` lanes. The delegation runs are proven to compute `fipsF`; `KeccakClean` proves that it is
`keccakF` (Clean's permutation). -/

namespace Spec

/-- The column parity `C[x]`. -/
def parity (A : Vector Lane 25) (x : Fin 5) : Lane :=
  A[lane x 0] ^^^ A[lane x 1] ^^^ A[lane x 2] ^^^ A[lane x 3] ^^^ A[lane x 4]

def theta (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p => A[p] ^^^ thetaD (parity A) (laneX p)
def rho (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p => A[p].rotateLeft (rhoOffset (laneX p) (laneY p))
def pi (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p => A[piSrc p]
def chi (A : Vector Lane 25) : Vector Lane 25 := Vector.ofFn fun p =>
  A[p] ^^^ (~~~A[lane (laneX p + 1) (laneY p)] &&& A[lane (laneX p + 2) (laneY p)])
def iota (r : Fin 24) (A : Vector Lane 25) : Vector Lane 25 := A.set 0 (A[0] ^^^ RC r)

def keccakRound (r : Fin 24) (A : Vector Lane 25) : Vector Lane 25 := iota r (chi (pi (rho (theta A))))

/-- Keccak-f[1600]: the 24 rounds. -/
def fipsF (A : Vector Lane 25) : Vector Lane 25 := (List.finRange 24).foldl (fun A r => keccakRound r A) A

end Spec
