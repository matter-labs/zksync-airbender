import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.KeccakUncached.Typed
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.KeccakUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data1 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf0).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw0).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf1).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw1).inputs)]

numeric_functional_base_capture data5 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf2).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw2).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf3).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw3).inputs)]

numeric_functional_base_capture data9 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf4).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw4).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf5).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw5).inputs)]

numeric_functional_base_capture data13 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf6).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw6).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf7).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw7).inputs)]

numeric_functional_base_capture data17 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf8).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw8).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf9).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw9).inputs)]

numeric_functional_base_capture data21 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf10).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw10).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf11).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw11).inputs)]

numeric_functional_base_capture data25 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf12).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw12).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf13).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw13).inputs)]

numeric_functional_base_capture data29 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf14).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw14).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf15).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw15).inputs)]

numeric_functional_base_capture data33 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf16).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw16).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf17).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw17).inputs)]

numeric_functional_base_capture data37 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf18).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw18).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf19).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw19).inputs)]

numeric_functional_base_capture data41 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf20).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw20).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf21).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw21).inputs)]

numeric_functional_base_capture data45 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf22).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw22).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf23).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw23).inputs)]

numeric_functional_base_capture data49 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf24).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw24).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf25).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw25).inputs)]

numeric_functional_base_capture data53 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf26).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw26).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf27).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw27).inputs)]

numeric_functional_base_capture data57 := [
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf28).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw28).inputs),
  NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf29).isSome)),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw29).inputs)]

numeric_functional_base_capture data61 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw0 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw1 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw4 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw5 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_functional_base_capture data65 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw8 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw9 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw12 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw13 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_functional_base_capture data69 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw16 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw17 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw20 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw21 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_functional_base_capture data73 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw24 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw25 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw28 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

numeric_functional_base_capture data77 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw2 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw3 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw6 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw7 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_functional_base_capture data81 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw10 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw11 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw14 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw15 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_functional_base_capture data85 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw18 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw19 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw22 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw23 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_functional_base_capture data89 := [
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw26 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw27 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw29 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing),
  NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

noncomputable def data : List NumericFunctionalBaseChecks.Data := (((([projectionData] ++ (data1 ++ data5)) ++ (data9 ++ (data13 ++ data17))) ++ ((data21 ++ (data25 ++ data29)) ++ (data33 ++ (data37 ++ data41)))) ++ (((data45 ++ (data49 ++ data53)) ++ (data57 ++ (data61 ++ data65))) ++ ((data69 ++ (data73 ++ data77)) ++ (data81 ++ (data85 ++ data89)))))

end Airbender.Compiler.MemoryPayloadChecks.KeccakUncached
