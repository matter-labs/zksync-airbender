import Mathlib.Data.List.Basic

namespace Airbender.Keccak.Split

/-- The three workers called by the blessed split Keccak-f[1600] wrapper.
Their native circuit soundness and memory effects are separate obligations. -/
inductive Kind where
  | columnParity | thetaRho | chi5
  deriving DecidableEq, Repr

def Kind.mode : Kind → Nat
  | .columnParity => 0
  | .thetaRho => 3
  | .chi5 => 5

/-- CSR addresses from the public wrapper's three split registrations. -/
def Kind.csr : Kind → Nat
  | .columnParity => 0x7CD
  | .thetaRho => 0x7CC
  | .chi5 => 0x7CE

def roundPattern : List Kind :=
  List.replicate 5 .columnParity ++
  List.replicate 5 .thetaRho ++
  List.replicate 5 .chi5

/-- Twenty-four rounds of fifteen calls, then one delayed final parity call. -/
def schedule : List Kind :=
  (List.replicate 24 roundPattern).flatten ++ [.columnParity]

/-- This is the control encoding in the public Rust wrapper: 3 mode bits,
3 iteration bits and the round number beginning at bit six. -/
def encode (kind : Kind) (iteration round : Nat) : Nat :=
  kind.mode + 8 * iteration + 64 * round

def kindAt (index : Nat) : Kind :=
  if index = 360 then .columnParity
  else if index % 15 < 5 then .columnParity
  else if index % 15 < 10 then .thetaRho
  else .chi5

/-- The control word supplied before call `index`. The final parity call
starts in round 24, after the twenty-four complete rounds. -/
def controlAt (index : Nat) : Nat :=
  if index = 360 then encode .columnParity 0 24
  else encode (kindAt index) (index % 5) (index / 15)

/-- One valid split-worker call advances the public control schedule. -/
def bump (control : Nat) : Nat :=
  let mode := control % 8
  let iteration := control / 8 % 8
  let round := control / 64
  if iteration < 4 then control + 8
  else if mode = 0 then encode .thetaRho 0 round
  else if mode = 3 then encode .chi5 0 round
  else encode .columnParity 0 (round + 1)

end Airbender.Keccak.Split
