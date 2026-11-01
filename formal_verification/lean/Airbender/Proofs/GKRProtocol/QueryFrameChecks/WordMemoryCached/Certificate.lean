import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryCached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.WordMemoryCached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.originalProjection Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.fields Airbender.Compiler.QueryFrameNative.WordMemoryCached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.originalProjection Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.WordMemoryCached
