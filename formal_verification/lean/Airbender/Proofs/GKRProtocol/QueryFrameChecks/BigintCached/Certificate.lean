import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BigintCached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.BigintCached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.BigintCached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.BigintCached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.LookupSourceNative.BigintCached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.BigintCached.native.fields Airbender.Compiler.QueryFrameNative.BigintCached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.originalProjection Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.LookupSourceNative.BigintCached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.BigintCached
