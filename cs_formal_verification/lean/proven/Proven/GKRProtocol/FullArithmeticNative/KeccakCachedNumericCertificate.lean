module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericBindings
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericTraces
public import Proven.GKRProtocol.ArithmeticNormalizationTrace

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

noncomputable def numericTraceCapture : NumericArithmeticTrace.Capture 266 := ⟨numericCapture, numericTraceRows⟩

theorem numericTraceBindings : NumericArithmeticTrace.bindingCheck
    (NumericArithmeticTrace.pairs babyBearModulus numericCapture) numericTraceRows = true := by decide +kernel

theorem numericTraceChecked : NumericArithmeticTrace.check babyBearModulus numericTraceCapture = true := by decide +kernel

theorem numericChecked : NumericArithmeticChecks.check babyBearModulus numericCapture = true :=
  NumericArithmeticTrace.check_sound babyBearModulus numericTraceCapture numericTraceBindings numericTraceChecked

theorem numericFullChecked : FullArithmeticChecks.check native.addresses native.artifact native.certificate = true :=
  NumericArithmeticChecks.full_check _ _ _ _ numericBindings numericChecked

end Airbender.Compiler.FullArithmeticNative.KeccakCached
