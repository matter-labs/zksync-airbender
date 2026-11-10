import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BigintCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks

namespace Airbender.Compiler.HelperPayloadChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalEntries := [
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate16
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate18
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate19
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate20
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate21
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate22
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate23
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate24
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate25
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate26
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate27
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate28
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate29
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate30
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate31
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate32
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate33
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate34
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate35
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate36
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate37
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate38
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate39
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate40
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate41
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate42
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate43
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate44
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate45
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate46
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate47
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate48
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate49
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate50
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate51
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate52
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate53
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate54
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate55
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate56
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing,
  NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintCached.native.candidate57
  Airbender.Compiler.HelperNative.BigintCached.native.placement Airbender.Compiler.MemoryNative.BigintCached.native.bank
  Airbender.Compiler.ConsumerNative.BigintCached.native.typing]

end Airbender.Compiler.HelperPayloadChecks.BigintCached
