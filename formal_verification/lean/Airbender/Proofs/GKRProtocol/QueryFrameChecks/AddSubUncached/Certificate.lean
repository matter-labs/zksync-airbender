import Airbender.Proofs.GKRProtocol.QueryFrameChecks.AddSubUncached.Bindings

namespace Airbender.Compiler.QueryFrameChecks.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

theorem checked : NumericQueryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.AddSubUncached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound_of_binding data Airbender.Compiler.QueryFrameNative.AddSubUncached.native.fields Airbender.Compiler.QueryFrameNative.AddSubUncached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.originalProjection Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank
    source_binding checked

end Airbender.Compiler.QueryFrameChecks.AddSubUncached
