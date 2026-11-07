import Airbender.Review.Helpers.Tables.PairData

namespace Airbender.Verification

/- Fixed contents are projections of complete native JSON regions. -/
def regIsZeroTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  setupPairTable "Airbender.RegIsZero" regZeroData (by decide)

def u16SignTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  setupPairTable "Airbender.U16GetSign" signData (by decide)

def u16LowByteTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  setupPairTable "Airbender.U16GetLowByte" lowByteData (by decide)

def pairLookup {p : Nat} [Fact p.Prime] (table : Table (ZMod p) fieldPair)
    (key value : Expression (ZMod p)) : Lookup (ZMod p) where
  table := table.toRaw
  entry := #v[key, value]


end Airbender.Verification
