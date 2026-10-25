import GKRProtocol.DecoderArgumentsNative.UnifiedUncached

namespace Tests.GKRDecoderArguments
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private noncomputable def clean := Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.placement
private noncomputable def fullBank := Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank
private noncomputable def sourceBank := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank

theorem wrong_execute_rejected :
    CleanExpression.nativeCheck (.const 1) clean fullBank
      Airbender.Compiler.LookupNative.UnifiedUncached.native.field18_0.lowered sourceBank = false := by
  decide +kernel

theorem omitted_funct3_rejected :
    CleanExpression.nativeCheck (.const 0) clean fullBank
      Airbender.Compiler.LookupNative.UnifiedUncached.native.field18_8.lowered sourceBank = false := by
  decide +kernel

theorem changed_mask_rejected :
    CleanExpression.nativeCheck
      (.mul (.const 2) (decoderFlagExpression UnifiedReduced.importedConstraintsDecoderColumns)) clean fullBank
      Airbender.Compiler.LookupNative.UnifiedUncached.native.field18_9.lowered sourceBank = false := by
  decide +kernel

theorem wrong_tag_rejected :
    CleanExpression.nativeCheck (.const 47) clean fullBank
      Airbender.Compiler.LookupNative.UnifiedUncached.native.field18_10.lowered sourceBank = false := by
  decide +kernel

end Tests.GKRDecoderArguments
