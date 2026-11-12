module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.WordMemoryCached.Typed
public import Proven.GKRProtocol.MemoryPayloadChecks.WordMemoryCached.ProjectionData
public import Proven.Import.GKRProtocol.NumericFunctionalBaseImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.WordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [0] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [1] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [2] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [3] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [4] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [5] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [6] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryCached.native.definitions [7] Airbender.Compiler.MemoryNative.WordMemoryCached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw0 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw1 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw4 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw5 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing [(GKRAddress.InnerLayer 2 4)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw2 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw3 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw6 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.MemoryNative.WordMemoryCached.native.raw7 Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing [(GKRAddress.InnerLayer 2 4)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ data9)) ++ ((data13 ++ data17) ++ (data21 ++ data25)))

end Airbender.Compiler.MemoryPayloadChecks.WordMemoryCached
