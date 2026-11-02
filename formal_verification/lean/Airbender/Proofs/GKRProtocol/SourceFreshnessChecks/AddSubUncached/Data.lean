import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.AddSubUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.SourceFreshnessChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 0))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 1))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 2))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 3))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 4))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 5))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 6))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 7)))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 8))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 9))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 10))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 11))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 12))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 13))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 14))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 15)))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 16))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 17))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 18))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 19))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 20))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 21))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 22))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 23)))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 24))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 25))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 26))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 27))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 28))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 29))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 30))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 31)))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 32))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 33))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 34))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 35))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 36))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 37))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 38))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 39)))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 40))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address (Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement 41)))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((data0 ++ (data8 ++ data16)) ++ (data24 ++ (data32 ++ data40)))

numeric_functional_base_capture targetData := [NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 21)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 19)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 20))]

end Airbender.Compiler.SourceFreshnessChecks.AddSubUncached
