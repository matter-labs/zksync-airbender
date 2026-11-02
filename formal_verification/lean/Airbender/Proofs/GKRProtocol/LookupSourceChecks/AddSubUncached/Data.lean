import Airbender.Proofs.GKRProtocol.LookupSourceChecks.AddSubUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.LookupSourceChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field0_0 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field2_0 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field3_0 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field4_0 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field5_0 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_0 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_1 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_2 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_3 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank)]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_4 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_5 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_6 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_7 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field14_8 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.AddSubUncached.native.recipe14_0.inputs.headD (.BaseLayerWitness 0)), .base))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.field16_0 Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.leaf15.isSetup)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (decide (((Airbender.Compiler.LookupNative.AddSubUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericQueries.length + 1))))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.leaf1.isSetup)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 45) (decide (((Airbender.Compiler.LookupNative.AddSubUncached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.length + 1)))))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((data0 ++ data8) ++ (data16 ++ (data24 ++ data32)))

end Airbender.Compiler.LookupSourceChecks.AddSubUncached
