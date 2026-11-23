module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.JumpBranchCached.Typed
public import Proven.GKRProtocol.MemoryPayloadChecks.JumpBranchCached.ProjectionData
public import Proven.Import.GKRProtocol.NumericFunctionalBaseImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [0] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [1] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [2] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [3] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [4] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [5] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [6] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [7] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw0 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw1 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw4 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw5 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing [(GKRAddress.InnerLayer 2 0)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw2 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw3 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw6 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw7 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing [(GKRAddress.InnerLayer 2 0)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ data9)) ++ ((data13 ++ data17) ++ (data21 ++ data25)))

end Airbender.Compiler.MemoryPayloadChecks.JumpBranchCached
