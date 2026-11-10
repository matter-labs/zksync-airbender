import Airbender.Proofs.GKRProtocol.LookupSourceChecks.AddSubCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericLookupSourceChecks

namespace Airbender.Compiler.LookupSourceChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field0_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field2_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field3_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field4_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field5_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_1 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_2 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_3 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_4 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_5 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_6 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_7 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_8 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.ConsumerNative.AddSubCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_0.inputs.headD (.BaseLayerWitness 0)), .base)),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field16_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf15.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf1.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.length + 1))))]

end Airbender.Compiler.LookupSourceChecks.AddSubCached
