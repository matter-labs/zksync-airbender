module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.MulDivCached.Inputs
public import Proven.GKRProtocol.NumericNativePayloadChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate8
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate10
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate11
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate12
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate13
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate14
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate15
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate25
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.MulDivCached
