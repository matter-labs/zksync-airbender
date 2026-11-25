module
public import Human.Circuits.UnifiedReduced.Proth120Artifact
public import Proven.OpIndex
public import Proven.CircuitField

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

theorem radix_inverse : (2 ^ 128 * montgomeryInverse) % proth120Modulus = 1 := CircuitField.radix_inverse (p := proth120Modulus)

theorem signedScalar_cast (raw : BoundedNat proth120Modulus) :
    (signedScalar raw : ZMod proth120Modulus) =
      (raw.val : ZMod proth120Modulus) * (montgomeryInverse : ZMod proth120Modulus) := CircuitField.signedScalar_cast raw.val

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 120 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 20 := rfl

theorem timestamp_count {p : Nat} [Fact p.Prime] : (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

set_option maxRecDepth 100000 in
derive_op_index Airbender.UnifiedReduced.Proth120.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.UnifiedReduced.Proth120.importedConstraintsTimestampLookups

end Airbender.UnifiedReduced.Proth120
