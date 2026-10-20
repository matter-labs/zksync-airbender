import Human.Helpers.Context.PCState.Model

-- The statements proven in slop/Slop/Final/Helpers/Context/PCState/Theorems.lean (checked by verify.sh).

namespace Airbender.PCState

/-- Shared PC-range discharge for any circuit family. The circuit supplies its
    final low-limb bound; the logical global interface supplies the high bound.
    Both decoder inputs and the terminal-state boundary are covered. -/
def OutgoingBoundsClaim : Prop :=
  ∀ {p n : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p) {context : Context p n} (interface : Interface context) {pc : ZMod p × ZMod p} (outgoing : Outgoing context pc) (lowBound : pc.1.val < Arithmetic.limbBase),
    pc.1.val < Arithmetic.limbBase ∧ pc.2.val < Arithmetic.limbBase

end Airbender.PCState
