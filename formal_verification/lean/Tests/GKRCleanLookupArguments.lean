import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.Constraints

namespace Tests.GKRCleanLookupArguments
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem rejects_changed_range_argument :
    CleanExpression.nativeCheck
      (.add CleanArgumentsNative.AddSubUncached.native.rangeExpression0 (.const 1))
      CleanArithmeticNative.AddSubUncached.native.placement
      FullArithmeticNative.AddSubUncached.native.bank
      LookupNative.AddSubUncached.native.field0_0.lowered
      LookupSourceNative.AddSubUncached.native.bank = false := by decide +kernel

theorem rejects_changed_setup_tag :
    CleanExpression.nativeCheck
      (.add CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_8 (.const 1))
      CleanArithmeticNative.WordMemoryUncached.native.placement
      FullArithmeticNative.WordMemoryUncached.native.bank
      LookupNative.WordMemoryUncached.native.field0_8.lowered
      LookupSourceNative.WordMemoryUncached.native.bank = false := by decide +kernel

theorem rejects_changed_helper_argument :
    CleanExpression.nativeCheck
      (.add CleanArgumentsNative.AddSubUncached.native.timestampExpression0 (.const 1))
      CleanArithmeticNative.AddSubUncached.native.placement
      FullArithmeticNative.AddSubUncached.native.bank
      (HelperNative.AddSubUncached.native.recipe6.expression MemoryNative.AddSubUncached.native.bank.placement)
      MemoryNative.AddSubUncached.native.bank = false := by decide +kernel

private theorem last_range_bound : (65535 : Source.BaseField).val < 65536 := by decide +kernel
private theorem first_range_overflow : ¬(65536 : Source.BaseField).val < 65536 := by decide +kernel

theorem actual_range_accepts_last_value (environment : Environment Source.BaseField) :
    (Verification.range16 (.const 65535)).Contains environment :=
  clean_range16_lookup _ environment last_range_bound

theorem actual_range_rejects_first_overflow (environment : Environment Source.BaseField) :
    ¬(Verification.range16 (.const 65536)).Contains environment := by
  intro member
  have bound := Verification.range16_bound member
  change (65536 : Source.BaseField).val < 65536 at bound
  exact first_range_overflow bound

end Tests.GKRCleanLookupArguments
