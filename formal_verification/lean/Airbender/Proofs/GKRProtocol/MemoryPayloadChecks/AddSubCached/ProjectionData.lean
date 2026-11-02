import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.AddSubCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture projectionChunk0 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.AddSubCached.native.bank Airbender.Compiler.ConsumerNative.AddSubCached.native.typing ((Airbender.Compiler.MemoryNative.AddSubCached.native.projectionInputs.drop 0).take 6))]

noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=
  ⟨(projectionChunk0.getD 0 ⟨[], [], []⟩).ports, [], []⟩

end Airbender.Compiler.MemoryPayloadChecks.AddSubCached
