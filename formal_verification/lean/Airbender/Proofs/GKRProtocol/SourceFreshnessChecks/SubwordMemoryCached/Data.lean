import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.SubwordMemoryCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.SourceFreshnessChecks.SubwordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 0))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 1))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 2))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 3))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 4))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 5))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 6))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 7)))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 8))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 9))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 10))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 11))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 12))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 13))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 14))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 15)))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 16))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 17))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 18))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 19))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 20))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 21))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 22))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 23)))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 24))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 25))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 26))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 27))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 28))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 29))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 30))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 31)))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 32))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 33))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 34))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 35))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 36))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 37))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 38))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 39)))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 40))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 41))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 42))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 43))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 44))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 45))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 46))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 47)))]

numeric_functional_base_capture data48 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 48))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 49))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 50))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 51))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 52))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 53))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 54))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 55)))]

numeric_functional_base_capture data56 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 56))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 57))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 58))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 59))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 60))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement 61)))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (((data0 ++ data8) ++ (data16 ++ data24)) ++ ((data32 ++ data40) ++ (data48 ++ data56)))

numeric_functional_base_capture targetData := [NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 16)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 14)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 15))]

end Airbender.Compiler.SourceFreshnessChecks.SubwordMemoryCached
