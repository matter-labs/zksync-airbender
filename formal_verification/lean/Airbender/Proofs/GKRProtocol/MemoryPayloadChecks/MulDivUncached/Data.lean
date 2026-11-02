import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.MulDivUncached.Typed
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.MulDivUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.MulDivUncached.native.definitions [] Airbender.Compiler.MemoryNative.MulDivUncached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing (Airbender.Compiler.MemoryNative.MulDivUncached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw0 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw1 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw4 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw5 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing [(GKRAddress.InnerLayer 2 0)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw2 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw3 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw6 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryNative.MulDivUncached.native.raw7 Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.MulDivUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.ConsumerNative.MulDivUncached.native.typing [(GKRAddress.InnerLayer 2 0)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ data9)) ++ ((data13 ++ data17) ++ (data21 ++ data25)))

end Airbender.Compiler.MemoryPayloadChecks.MulDivUncached
