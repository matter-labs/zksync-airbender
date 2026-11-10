module
public import Mathlib.Data.List.Basic

@[expose] public section

namespace Airbender.Keccak.Split

/-- The three workers of the split Keccak-f[1600] protocol. -/
inductive Kind where
  | columnParity | thetaRho | chi5
  deriving DecidableEq, Repr

/-- The mode field of the control word that selects each worker. -/
def Kind.mode : Kind → Nat
  | .columnParity => 0
  | .thetaRho => 3
  | .chi5 => 5

/-- The x10 control word: 3 mode bits, 3 iteration bits, the round from bit six. -/
def encode (kind : Kind) (iteration round : Nat) : Nat :=
  kind.mode + 8 * iteration + 64 * round

/-- The worker of call `index` in `schedule`. -/
def kindAt (index : Nat) : Kind :=
  if index = 360 then .columnParity
  else if index % 15 < 5 then .columnParity
  else if index % 15 < 10 then .thetaRho
  else .chi5

/-- The control word in x10 before call `index`. The final parity call is in round 24. -/
def controlAt (index : Nat) : Nat :=
  if index = 360 then encode .columnParity 0 24
  else encode (kindAt index) (index % 5) (index / 15)

/-- The control word a worker writes back: the next call's control. -/
def bump (control : Nat) : Nat :=
  let mode := control % 8
  let iteration := control / 8 % 8
  let round := control / 64
  if iteration < 4 then control + 8
  else if mode = 0 then encode .thetaRho 0 round
  else if mode = 3 then encode .chi5 0 round
  else encode .columnParity 0 (round + 1)

end Airbender.Keccak.Split
