import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryUncached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryUncached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.originalProjection Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.fields Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.originalProjection Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.SubwordMemoryUncached
