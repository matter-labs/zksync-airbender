import Airbender.Proofs.GKRProtocol.LookupSourceChecks.WordMemoryUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericLookupSourceChecks

namespace Airbender.Compiler.LookupSourceChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field0_0 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_0 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_1 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_2 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_3 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_4 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_5 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_6 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_7 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_8 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field10_9 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.recipe10_0.inputs.headD (.BaseLayerWitness 0)), .base)),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field12_0 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field14_0 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_0 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_1 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_2 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_3 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_4 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_5 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_6 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_7 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.field15_8 Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf11.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 50) (decide (((Airbender.Compiler.LookupNative.WordMemoryUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 50) (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf1.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 50) (decide (((Airbender.Compiler.LookupNative.WordMemoryUncached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries.length + 1))))]

end Airbender.Compiler.LookupSourceChecks.WordMemoryUncached
