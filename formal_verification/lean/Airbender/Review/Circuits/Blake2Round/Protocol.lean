import Airbender.Review.Helpers.Core.Word

namespace Airbender.Blake2Round

/-- x12 after `i` native calls: the three request flags stay fixed, while the
    round bit shifts left and wraps after ten calls. -/
def controlAt (flags : Fin 8) (i : Nat) : Arithmetic.Word :=
  ⟨0, flags.val + 8 * (2 ^ i % 1024)⟩

end Airbender.Blake2Round
