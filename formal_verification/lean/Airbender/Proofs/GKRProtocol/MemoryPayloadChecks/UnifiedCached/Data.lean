import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedCached.Typed
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedCached.ProjectionData
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [0] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [1] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [2] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [3] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [4] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [5] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [6] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [7] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf8).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf9).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9).inputs)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf10).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf11).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11).inputs)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_functional_base_capture data29 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_functional_base_capture data33 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_functional_base_capture data37 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ (data9 ++ data13))) ++ ((data17 ++ (data21 ++ data25)) ++ (data29 ++ (data33 ++ data37))))

end Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
