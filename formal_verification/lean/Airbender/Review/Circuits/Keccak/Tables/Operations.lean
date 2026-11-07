import Clean.Specs.Keccak256

namespace Airbender.Keccak

def adjustedConstant (round : Nat) : Nat :=
  if h : 0 < round ∧ round ≤ 24 then
    Specs.Keccak256.roundConstants[round - 1].toNat else 0

def iotaByte (control : Nat) : Nat :=
  (adjustedConstant (control % 32) / 2 ^ (8 * (control / 32))) % 256

/-- Intended consequences of one tagged native query. These are properties of
    Clean membership, not another constraint interpreter. Tag zero is padding;
    rotation returns the two non-overlapping pieces of a packed 16-bit word. -/
def ByteOperationFacts (tag a b c : Nat) : Prop :=
  if tag = 0 then a = 0 ∧ b = 0 ∧ c = 0
  else if tag = 40 then
    a < 1048576 ∧ b < 65536 ∧ c < 65536 ∧
    b = (a % 65536) / 2 ^ (16 - a / 65536) ∧
    c = ((a % 65536) * 2 ^ (a / 65536)) % 65536
  else a < 256 ∧ b < 256 ∧ c < 256 ∧
    c = (if tag = 38 then a ^^^ iotaByte b
      else if tag = 39 then (a ^^^ 255) &&& b else a ^^^ b)

end Airbender.Keccak
