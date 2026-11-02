import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.ShiftBinopUncached.Typed
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.ShiftBinopUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.definitions [] Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing (Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw0 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw1 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw4 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw5 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing [(GKRAddress.InnerLayer 2 0)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw2 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw3 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw6 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.raw7 Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing [(GKRAddress.InnerLayer 2 0)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ data9)) ++ ((data13 ++ data17) ++ (data21 ++ data25)))

end Airbender.Compiler.MemoryPayloadChecks.ShiftBinopUncached
