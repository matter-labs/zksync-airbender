module
public import Human.Circuits.Bigint.Artifact
public import Human.Circuits.Bigint.Tables.Setup
public import Human.Helpers.Properties
public import Human.Circuits.Bigint.Addresses

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Bigint/Addresses.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Bigint.Addresses
open Arithmetic
/-- Canonical pointer limbs remain a register-interface obligation. Distinct
    pointers and RAM-only access belong to the full call, not this projection. -/
def InterfaceAssumptions (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop :=
  input.left.Bounded ∧ input.right.Bounded
def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setupTable)
  represents := Mapping
end Airbender.Bigint.Addresses
