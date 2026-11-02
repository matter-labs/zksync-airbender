import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.MulDivUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate8
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate10
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate11
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate12
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate13
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate14
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate15
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivUncached.native.candidate25
  Airbender.Compiler.HelperNative.MulDivUncached.native.placement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.MulDivUncached
