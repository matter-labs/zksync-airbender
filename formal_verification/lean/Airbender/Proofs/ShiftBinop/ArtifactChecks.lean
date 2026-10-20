import Airbender.Review.Circuits.ShiftBinop.RoutingModel

namespace Airbender.ShiftBinop
set_option autoImplicit false

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 50 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 12 := rfl

end Airbender.ShiftBinop
