import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.WordMemoryUncached.Typed
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.WordMemoryUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw0 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw1 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw4 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw5 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing [(GKRAddress.InnerLayer 2 4)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw2 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw3 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw6 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw7 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing [(GKRAddress.InnerLayer 2 4)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ data9)) ++ ((data13 ++ data17) ++ (data21 ++ data25)))

end Airbender.Compiler.MemoryPayloadChecks.WordMemoryUncached
