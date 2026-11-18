module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.ShiftBinopCachedNumericBindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem numericChecked : NumericArithmeticChecks.check babyBearModulus numericCapture = true := by decide +kernel

theorem numericFullChecked : FullArithmeticChecks.check native.addresses native.artifact native.certificate = true :=
  NumericArithmeticChecks.full_check _ _ _ _ numericBindings numericChecked

end Airbender.Compiler.FullArithmeticNative.ShiftBinopCached
