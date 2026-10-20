import Slop.UnifiedReduced.ControlLookups
import Slop.UnifiedReduced

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem control_lookup_values [Fact p.Prime] (hp : 4194304 ≤ p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 21 + w 22 + w 23 + w 24 = 1)
    (binary : w 26 = 0 ∧ w 27 = 0) (rom : w 87 = 0) :
    w 57 = (if (w 78 + w 79).val = 0 then 1 else 0) ∧
    w 58 = (((w 37).val / 32768 : Nat) : ZMod p) ∧
    w 61 = (((w 60).val / 32768 : Nat) : ZMod p) ∧
    (w 61 + 2 * w 58 + 4 * w 53 + 8 * w 57 + 16 * w 10).val < 128 ∧
    w 59 = (Verification.conditionalValue (Setup.conditionalKey
      (w 61 + 2 * w 58 + 4 * w 53 + 8 * w 57 + 16 * w 10).val) : ZMod p) ∧
    w 56 = (((w 81).val / 2 % 2 : Nat) : ZMod p) ∧
    w 30 = (((w 81).val - (w 81).val % 4 : Nat) : ZMod p) := by
  have equation (i : Fin 40) := Verification.assertion_of_holds holds
    ⟨48 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have zt := equation 0; have zk := equation 1; have zv := equation 2
  have aTag := equation 4; have ak := equation 5; have av := equation 6
  have bt := equation 13; have bk := equation 14; have bv := equation 15
  have ct := equation 22; have ck := equation 23; have cv := equation 24
  have pt := equation 31; have pk := equation 32; have pv := equation 33; have pr := equation 34
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, binary.1, binary.2, rom] at zt zk zv aTag ak av bt bk bv ct ck cv pt pk pv pr
  have tags : w 88 = 1 ∧ w 92 = 5 ∧ w 101 = 5 ∧ w 110 = 51 ∧ w 119 = 2 := by
    constructor
    · linear_combination zt
    constructor
    · linear_combination aTag
    constructor
    · linear_combination bt
    constructor
    · linear_combination ct
    · linear_combination pt
  have values : w 89 = w 78 + w 79 ∧ w 90 = w 57 ∧
      w 93 = w 37 ∧ w 94 = w 58 ∧ w 102 = w 60 ∧ w 103 = w 61 ∧
      w 111 = w 61 + 2 * w 58 + 4 * w 53 + 8 * w 57 + 16 * w 10 ∧
      w 112 = w 59 ∧ w 120 = w 81 ∧ w 121 = w 56 ∧ w 122 = w 30 := by
    repeat' apply And.intro
    all_goals first
      | linear_combination zk | linear_combination zv | linear_combination ak
      | linear_combination av | linear_combination bk | linear_combination bv
      | linear_combination ck | linear_combination cv | linear_combination pk
      | linear_combination pv | linear_combination pr
  have query (i : Fin 5) := Verification.lookup_of_holds holds
    ⟨13 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  have zero := Verification.regIsZero_value (by omega : 131072 ≤ p)
    (Setup.Proofs.zero_lookup (by omega) (query 0)
      (by simpa [Expression.eval, Verification.environment] using tags.1))
  have signA := Verification.u16Sign_value (by omega : 65536 ≤ p)
    (Setup.Proofs.sign_lookup (by omega) (query 1)
      (by simpa [Expression.eval, Verification.environment] using tags.2.1))
  have signB := Verification.u16Sign_value (by omega : 65536 ≤ p)
    (Setup.Proofs.sign_lookup (by omega) (query 2)
      (by simpa [Expression.eval, Verification.environment] using tags.2.2.1))
  have condition := Setup.Proofs.conditional_lookup (by omega) (query 3)
    (by simpa [Expression.eval, Verification.environment] using tags.2.2.2.1)
  have cleanup := Verification.jumpCleanup_value (by omega : 65536 ≤ p)
    (Setup.Proofs.cleanup_lookup (by omega) (query 4)
      (by simpa [Expression.eval, Verification.environment] using tags.2.2.2.2))
  simpa [Expression.eval, Verification.environment, values.1, values.2.1, values.2.2.1,
    values.2.2.2.1, values.2.2.2.2.1, values.2.2.2.2.2.1, values.2.2.2.2.2.2.1,
    values.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.1, values.2.2.2.2.2.2.2.2.2.1,
    values.2.2.2.2.2.2.2.2.2.2] using
    And.intro zero.2 (And.intro signA.2 (And.intro signB.2
      (And.intro condition.1 (And.intro condition.2 (And.intro cleanup.2.1 cleanup.2.2)))))

end Airbender.UnifiedReduced.Proofs
