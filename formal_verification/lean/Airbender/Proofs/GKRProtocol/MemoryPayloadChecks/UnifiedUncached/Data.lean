import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedUncached.Typed
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf8).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw8).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf9).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw9).inputs)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf10).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw10).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedUncached.native.leaf11).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing (Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw11).inputs)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw10 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw11 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw8 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw9 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)]

numeric_functional_base_capture data29 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw0 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw1 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw4 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw5 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)]

numeric_functional_base_capture data33 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing [(GKRAddress.InnerLayer 2 0)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw2 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw3 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw6 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)]

numeric_functional_base_capture data37 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.MemoryNative.UnifiedUncached.native.raw7 Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing [(GKRAddress.InnerLayer 2 0)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ (data9 ++ data13))) ++ ((data17 ++ (data21 ++ data25)) ++ (data29 ++ (data33 ++ data37))))

end Airbender.Compiler.MemoryPayloadChecks.UnifiedUncached
