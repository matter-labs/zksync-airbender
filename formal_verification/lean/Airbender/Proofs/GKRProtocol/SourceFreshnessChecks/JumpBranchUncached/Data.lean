import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.JumpBranchUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.SourceFreshnessChecks.JumpBranchUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 0))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 1))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 2))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 3))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 4))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 5))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 6))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 7)))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 8))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 9))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 10))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 11))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 12))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 13))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 14))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 15)))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 16))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 17))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 18))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 19))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 20))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 21))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 22))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 23)))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 24))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 25))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 26))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 27))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 28))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 29))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 30))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 31)))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 32))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 33))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 34))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 35))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 36))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 37))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 38))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 39)))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 40))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 41))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 42))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 43))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 44))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 45))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 46))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 47)))]

numeric_functional_base_capture data48 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.LookupNative.JumpBranchUncached.native.sourcePlacement 48)))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((data0 ++ (data8 ++ data16)) ++ ((data24 ++ data32) ++ (data40 ++ data48)))

numeric_functional_base_capture targetData := [NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 28)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 26)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 27))]

end Airbender.Compiler.SourceFreshnessChecks.JumpBranchUncached
