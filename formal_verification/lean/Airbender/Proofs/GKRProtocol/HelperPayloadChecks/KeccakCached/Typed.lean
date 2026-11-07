import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.KeccakCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate0
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate2
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate3
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate4
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate5
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate6
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate7
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate8
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate9
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate10
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate11
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate12
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate13
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate14
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate15
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate16
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate17
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate18
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate19
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate20
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate21
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate22
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate23
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate24
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate25
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate26
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate27
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate28
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate29
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate72
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.KeccakCached
