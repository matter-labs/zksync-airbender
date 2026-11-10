import Airbender.Import.GKRProtocol.Source
import Airbender.Proofs.GKRProtocol.CounterMasked
import Airbender.Proofs.BabyBear

namespace Tests.GKRMaterializedCounters
open Airbender Airbender.Compiler
set_option warningAsError true

/-- A repeated query consumes two units of the actual setup multiplicity. -/
theorem repeated_queries_cancel :
    (([RationalPair.leaf 1 3, RationalPair.leaf 1 3,
      RationalPair.leaf (-2) 3] : List (RationalPair Source.BaseField))).sum.numerator = 0 := by
  decide +kernel

theorem rejects_missing_multiplicity :
    (([RationalPair.leaf 1 3, RationalPair.leaf 1 3,
      RationalPair.leaf (-1) 3] : List (RationalPair Source.BaseField))).sum.numerator ≠ 0 := by
  decide +kernel

/-- Zero denominators remain defined in the exact polynomial relation. -/
theorem zero_challenge_needs_no_inverse :
    (balancedLookupGroup (0 : Source.BaseField) [1, 2]).sum.numerator = 0 :=
  balancedLookupGroup_zero _ _

theorem disabled_unmatched_query_is_zero :
    (([RationalPair.leaf 0 17, RationalPair.leaf 0 29] :
      List (RationalPair Source.BaseField))).sum.numerator = 0 := by decide +kernel

end Tests.GKRMaterializedCounters
