import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.KeccakUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate0
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate2
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate3
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate4
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate5
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate6
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate7
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate8
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate9
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate10
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate11
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate12
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate13
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate14
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate15
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate16
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate17
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate18
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate19
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate20
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate21
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate22
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate23
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate24
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate25
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate26
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate27
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate28
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate29
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakUncached.native.candidate72
  Airbender.Compiler.HelperNative.KeccakUncached.native.placement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.KeccakUncached
