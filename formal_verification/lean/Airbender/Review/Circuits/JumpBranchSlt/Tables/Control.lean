import Airbender.Review.Helpers.Tables.Lookups

namespace Airbender.Verification

def conditionalTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldPair :=
  setupPairTable "Airbender.ConditionalJmpBranchSlt" conditionalData (by decide)

def jumpCleanupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldTriple :=
  setupTripleTable "Airbender.JumpCleanupOffset" jumpCleanupData (by decide)

def jumpCleanup {p : Nat} [Fact p.Prime]
    (key bit1 cleaned : Expression (ZMod p)) : Lookup (ZMod p) where
  table := jumpCleanupTable.toRaw
  entry := #v[key, bit1, cleaned]

end Airbender.Verification
