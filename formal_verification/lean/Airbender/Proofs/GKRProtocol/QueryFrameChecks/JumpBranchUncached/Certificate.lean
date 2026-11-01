import Airbender.Proofs.GKRProtocol.QueryFrameChecks.JumpBranchUncached.Bindings
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.JumpBranchUncached.IndexedData

namespace Airbender.Compiler.QueryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel

theorem checked : NumericQueryFrameChecks.check data = true :=
  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding
    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked

theorem originalChecked : Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields.all (fun field =>
    erasureUntouched Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.coordinates (field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection) &&
      field.transportCheck Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement
        Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank) = true :=
  NumericQueryFrameChecks.check_sound data Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.fields Airbender.Compiler.QueryFrameNative.JumpBranchUncached.native.coordinates
    Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.originalProjection Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank
    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked

end Airbender.Compiler.QueryFrameChecks.JumpBranchUncached
