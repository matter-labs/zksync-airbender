import Airbender.Proofs.Blake2Round.NativeGAssignment

namespace Airbender.Blake2Round.Proofs

/- Pure projections used by column-value proofs. Keeping these definitions apart
   from membership soundness lets the checked column algebra stay cached. -/
def plainBase : Vector Nat 3 := #v[256, 128, 512]
def plainTags : Vector Nat 3 := #v[4, 19, 20]
def plainGKind : Vector (Fin 5) 3 := #v[0, 3, 4]
def carryTags : Vector Nat 2 := #v[55, 56]
def carryGKind : Vector (Fin 5) 2 := #v[0, 3]

def plainPad {p : Nat} (row : Vector (ZMod p) 6) : Vector (ZMod p) 9 :=
  #v[row[0], row[1], row[2], 0, 0, 0, 0, 0, row[5]]

def carryPad {p : Nat} (kind : Fin 2) (row : Vector (ZMod p) 6) : Vector (ZMod p) 9 :=
  #v[row[0], row[1], row[3], 0, 0, 0, 0, 0, ((#v[4, 19][kind] : Nat) : ZMod p)]

def combinedLowPad {p : Nat} (row : Vector (ZMod p) 6) : Vector (ZMod p) 9 :=
  #v[row[0], row[2], combinedLow row[4], 0, 0, 0, 0, 0, 18]

def combinedHighPad {p : Nat} (row : Vector (ZMod p) 6) : Vector (ZMod p) 9 :=
  #v[row[1], row[3], combinedHigh row[4], 0, 0, 0, 0, 0, 17]

end Airbender.Blake2Round.Proofs
