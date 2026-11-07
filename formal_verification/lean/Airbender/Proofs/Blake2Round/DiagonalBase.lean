import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Mathlib.Tactic.ReduceModChar

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true

/-- Both phases expose the same stable G assignment. Native storage is read by
    NativeLayout and NativeDiagonalAssignment, independently of the G proof. -/
abbrev diagonalGBase {p : Nat} [Fact p.Prime] := @nativeDiagonalBase p _
abbrev diagonalGAssignment {p : Nat} [Fact p.Prime] := @nativeDiagonalAssignment p _

end Airbender.Blake2Round.Proofs
