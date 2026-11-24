module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.WordMemoryCached.Typed
public import Proven.Import.GKRProtocol.NumericFunctionalBaseImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate2
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate4
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate5
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate6
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)]

numeric_functional_base_capture data4 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate7
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate8
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate9
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.WordMemoryCached.native.candidate13
  Airbender.Compiler.HelperNative.WordMemoryCached.native.placement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank
  Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (data0 ++ data4)

end Airbender.Compiler.HelperPayloadChecks.WordMemoryCached
