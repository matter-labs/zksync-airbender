module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.LookupSourceChecks.AddSubCached.Typed
public import Proven.Import.GKRProtocol.NumericFunctionalBaseImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.LookupSourceChecks.AddSubCached
open Airbender.Compiler
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field0_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field2_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field3_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field4_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field5_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_1 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_2 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_3 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank)]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_4 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_5 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_6 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_7 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_8 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.ConsumerNative.AddSubCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_0.inputs.headD (.BaseLayerWitness 0)), .base))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field16_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf15.isSetup)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.length + 1))))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf1.isSetup)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.length + 1)))))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((data0 ++ data8) ++ (data16 ++ (data24 ++ data32)))

end Airbender.Compiler.LookupSourceChecks.AddSubCached
