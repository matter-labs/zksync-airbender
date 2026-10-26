import Airbender.Proofs.GKRProtocol.CounterMasked
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.OracleFrameNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.QueryFrameNative.AddSubUncached
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

/-- The real full arithmetic bank does not contain the native setup address. -/
theorem rejects_setup_as_finite_arithmetic_input :
    addressEqual (FullArithmeticNative.AddSubUncached.native.bank.address
      (FullArithmeticNative.AddSubUncached.native.bank.placement (.Setup 0))) (.Setup 0) = false := by
  decide +kernel

theorem rejects_counter_alias_with_original_input :
    decide (42 ≤ (FullArithmeticNative.AddSubUncached.native.originalProjection 0).val) = false := by
  decide +kernel

theorem actual_range_row_contains_seven :
    MaterializedNative.AddSubUncached.native.model.Contains [.range16] [7] :=
  MaterializedRangeNative.AddSubUncached.native.range16_contains 7 (by decide +kernel)

theorem actual_timestamp_row_contains_last_value :
    MaterializedNative.AddSubUncached.native.model.Contains [.timestamp] [524287] :=
  MaterializedRangeNative.AddSubUncached.native.timestamp_contains 524287 (by decide +kernel)

theorem rejects_query_using_normalized_history :
    erasureUntouched QueryFrameNative.AddSubUncached.native.coordinates
      ((Source.EncodedField.input (.Variable
        (HistoryErasureNative.AddSubUncached.native.historyCells.get ⟨0, by decide⟩).val)).polynomial
          FullArithmeticNative.AddSubUncached.native.originalProjection) = false := by decide +kernel

theorem rejects_changed_original_projection :
    (Source.EncodedField.input (.Variable 1)).transportCheck (fun _ => ⟨0, by decide⟩)
      LookupNative.AddSubUncached.native.sourcePlacement FullArithmeticNative.AddSubUncached.native.inputBank
      LookupSourceNative.AddSubUncached.native.bank = false := by decide +kernel

end Tests.GKRMaterializedCounters
