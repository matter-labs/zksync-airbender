module
public import Human.Circuits.Keccak.Artifact
public import Human.Helpers.Properties
public import CleanCore.Specs.Keccak256
public import Human.Circuits.Keccak.Tables.Setup
public import Slop.Defs.Circuits.Keccak.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Keccak/Tables/Setup.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Keccak
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
/-- Every native byte query has bounded, exact outputs, including padding.
    The table contents remain the modeled setup defined above. -/
def ByteLookupChecks {p : Nat} [Fact p.Prime]
    (control : Fin 4096 → Vector Nat 6) (w : Nat → ZMod p) : Prop :=
  ∀ i : Fin 40,
    let entry := ((FlatOperation.lookups (importedConstraints (setupTable control))).get
      ⟨i.val + 2, by rw [lookup_count]; omega⟩).entry.toArray
    let value := fun j => (entry[j]!.eval (Verification.environment w)).val
    ByteOperationFacts (value 7) (value 0) (value 1) (value 2)
end Airbender.Keccak
