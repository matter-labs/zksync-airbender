import Airbender.Proofs.GKRProtocol.LookupSourceChecks.SubwordMemoryUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.LookupSourceChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field0_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field2_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field3_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank)]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_9 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_0.inputs.headD (.BaseLayerWitness 0)), .base))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field14_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field15_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank)]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank)]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank)]

numeric_functional_base_capture data48 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf13.isSetup)),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.length + 1))))),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf1.isSetup))]

numeric_functional_base_capture data56 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 64) (decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.length + 1)))))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (((data0 ++ data8) ++ (data16 ++ data24)) ++ ((data32 ++ data40) ++ (data48 ++ data56)))

end Airbender.Compiler.LookupSourceChecks.SubwordMemoryUncached
