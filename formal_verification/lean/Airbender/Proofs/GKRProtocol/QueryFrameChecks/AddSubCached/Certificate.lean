import Airbender.Proofs.GKRProtocol.QueryFrameChecks.AddSubCached.Bindings

namespace Airbender.Compiler.QueryFrameChecks.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

theorem checked : NumericQueryFrameChecks.check data = true := by decide +kernel

theorem originalChecked : Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.AddSubCached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound_of_binding data Airbender.Compiler.QueryFrameNative.AddSubCached.native.fields Airbender.Compiler.QueryFrameNative.AddSubCached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.originalProjection Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank
    source_binding checked

end Airbender.Compiler.QueryFrameChecks.AddSubCached
