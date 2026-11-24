module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.AddSubCached.Inputs
public import Proven.GKRProtocol.NumericMemoryPayloadChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

noncomputable def originalEntries : List NumericFunctionalBaseChecks.Data := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing Airbender.Compiler.MemoryNative.AddSubCached.native.projectionInputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [0] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [1] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw1).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [2] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [3] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw3).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [4] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [5] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw5).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [6] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.AddSubCached.native.definitions [7] Airbender.Compiler.MemoryNative.AddSubCached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing (Airbender.Compiler.MemoryNative.AddSubCached.native.raw7).inputs),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw0 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw1 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw4 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw5 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing [(GKRAddress.InnerLayer 2 0)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw2 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw3 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw6 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.MemoryNative.AddSubCached.native.raw7 Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing [(GKRAddress.InnerLayer 2 0)])]

end Airbender.Compiler.MemoryPayloadChecks.AddSubCached
