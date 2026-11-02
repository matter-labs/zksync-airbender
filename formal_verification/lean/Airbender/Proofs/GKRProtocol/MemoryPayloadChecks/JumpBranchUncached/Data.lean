import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.JumpBranchUncached.Typed
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.JumpBranchUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchUncached.native.definitions [] Airbender.Compiler.MemoryNative.JumpBranchUncached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw0 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw1 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw4 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw5 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing [(GKRAddress.InnerLayer 2 0)]),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw2 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw3 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw6 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryNative.JumpBranchUncached.native.raw7 Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.JumpBranchUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing [(GKRAddress.InnerLayer 2 0)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((([projectionData] ++ data1) ++ (data5 ++ data9)) ++ ((data13 ++ data17) ++ (data21 ++ data25)))

end Airbender.Compiler.MemoryPayloadChecks.JumpBranchUncached
