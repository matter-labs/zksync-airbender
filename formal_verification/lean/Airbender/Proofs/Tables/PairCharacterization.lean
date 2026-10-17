import Airbender.Review.Helpers.Tables.Lookups
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control
import Airbender.Proofs.Tables.ImportedPairs
import Airbender.Proofs.Tables.ImportedControl
import Airbender.Proofs.Tables.ImportedCleanup

namespace Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def pairTable {p : Nat} [Fact p.Prime] (name : String)
    (length : Nat) (value : Nat → Nat) : Table (ZMod p) fieldPair := .fromStatic {
  name := name
  length := length
  row i := ((i.val : ZMod p), (value i.val : ZMod p))
  index x := x.1.val
  Spec x := ∃ i : Fin length, x = ((i.val : ZMod p), (value i.val : ZMod p))
  contains_iff _ := Iff.rfl
}

def referenceJumpCleanupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) fieldTriple := .fromStatic {
  name := "Airbender.JumpCleanupOffset"
  length := 65536
  row i := ((i.val : ZMod p), ((i.val / 2 % 2 : Nat) : ZMod p), ((i.val - i.val % 4 : Nat) : ZMod p))
  index x := x.1.val
  Spec x := ∃ i : Fin 65536,
    x = ((i.val : ZMod p), ((i.val / 2 % 2 : Nat) : ZMod p), ((i.val - i.val % 4 : Nat) : ZMod p))
  contains_iff _ := Iff.rfl
}

@[simp] theorem regIsZeroTable_characterization {p : Nat} [Fact p.Prime] :
    (regIsZeroTable : Table (ZMod p) fieldPair) = pairTable "Airbender.RegIsZero" 131072 (fun n => if n = 0 then 1 else 0) := by
  unfold regIsZeroTable setupPairTable pairTable
  simp only [ImportedPairs.regZero_row]
  rfl

@[simp] theorem u16SignTable_characterization {p : Nat} [Fact p.Prime] :
    (u16SignTable : Table (ZMod p) fieldPair) = pairTable "Airbender.U16GetSign" 65536 (fun n => n / 32768) := by
  unfold u16SignTable setupPairTable pairTable
  simp only [ImportedPairs.sign_row]
  rfl

@[simp] theorem u16LowByteTable_characterization {p : Nat} [Fact p.Prime] :
    (u16LowByteTable : Table (ZMod p) fieldPair) = pairTable "Airbender.U16GetLowByte" 65536 (fun n => n % 256) := by
  unfold u16LowByteTable setupPairTable pairTable
  simp only [ImportedPairs.lowByte_row]
  rfl

@[simp] theorem conditionalTable_characterization {p : Nat} [Fact p.Prime] :
    (conditionalTable : Table (ZMod p) fieldPair) = pairTable "Airbender.ConditionalJmpBranchSlt" 4194304 conditionalValue := by
  unfold conditionalTable setupPairTable pairTable
  simp only [ImportedControl.conditional_row]
  rfl

@[simp] theorem jumpCleanupTable_characterization {p : Nat} [Fact p.Prime] :
    (jumpCleanupTable : Table (ZMod p) fieldTriple) = referenceJumpCleanupTable := by
  unfold jumpCleanupTable setupTripleTable referenceJumpCleanupTable
  simp only [ImportedCleanup.cleanup_row]
  rfl

end Airbender.Verification
