import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.MulDivCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.SourceFreshnessChecks.MulDivCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 0))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 1))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 2))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 3))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 4))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 5))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 6))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 7)))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 8))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 9))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 10))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 11))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 12))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 13))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 14))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 15)))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 16))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 17))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 18))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 19))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 20))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 21))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 22))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 23)))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 24))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 25))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 26))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 27))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 28))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 29))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 30))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 31)))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 32))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 33))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 34))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 35))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 36))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 37))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 38))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 39)))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 40))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 41))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 42))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 43))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 44))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 45))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 46))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 47)))]

numeric_functional_base_capture data48 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 48))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 49))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 50))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 51))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 52))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 53))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 54))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 55)))]

numeric_functional_base_capture data56 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 56))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 57))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 58))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 59))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 60))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 61))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 62))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 63)))]

numeric_functional_base_capture data64 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address (Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement 64)))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (((data0 ++ data8) ++ (data16 ++ data24)) ++ ((data32 ++ data40) ++ (data48 ++ (data56 ++ data64))))

numeric_functional_base_capture targetData := [NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 23)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 21)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 22))]

end Airbender.Compiler.SourceFreshnessChecks.MulDivCached
