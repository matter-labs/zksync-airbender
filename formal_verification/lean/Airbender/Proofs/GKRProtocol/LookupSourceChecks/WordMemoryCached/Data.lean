import Airbender.Proofs.GKRProtocol.LookupSourceChecks.WordMemoryCached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.LookupSourceChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field0_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_1 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_2 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_3 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank)]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_4 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_5 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_6 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_7 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_8 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_9 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_0.inputs.headD (.BaseLayerWitness 0)), .base))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field12_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field14_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_1 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank)]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_2 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_3 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_4 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_5 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_6 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_7 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_8 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf11.isSetup))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.length + 1))))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf1.isSetup)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 52) (decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.length + 1)))))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((data0 ++ (data8 ++ data16)) ++ (data24 ++ (data32 ++ data40)))

end Airbender.Compiler.LookupSourceChecks.WordMemoryCached
