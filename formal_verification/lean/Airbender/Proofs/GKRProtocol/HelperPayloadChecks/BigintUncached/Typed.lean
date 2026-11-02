import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BigintUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate16
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate18
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate19
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate20
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate21
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate22
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate23
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate24
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate25
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate26
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate27
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate28
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate29
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate30
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate31
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate32
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate33
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate34
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate35
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate36
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate37
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate38
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate39
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate40
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate41
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate42
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate43
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate44
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate45
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate46
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate47
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate48
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate49
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate50
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate51
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate52
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate53
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate54
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate55
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate56
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate57
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.BigintUncached
