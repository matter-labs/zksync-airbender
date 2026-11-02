import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture projectionChunk0 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 0).take 8))]

numeric_functional_base_capture projectionChunk8 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 8).take 8))]

noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=
  ⟨((projectionChunk0.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk8.getD 0 ⟨[], [], []⟩).ports), [], []⟩

end Airbender.Compiler.MemoryPayloadChecks.UnifiedUncached
