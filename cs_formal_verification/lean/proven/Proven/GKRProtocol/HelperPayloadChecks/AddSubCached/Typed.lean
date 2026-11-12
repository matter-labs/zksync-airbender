module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.AddSubCached.Inputs
public import Proven.GKRProtocol.NumericNativePayloadChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate6
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate8
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate9
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate10
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate11
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate12
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate13
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate17
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.AddSubCached
