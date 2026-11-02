import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.KeccakCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture projectionChunk0 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.ConsumerNative.KeccakCached.native.typing ((Airbender.Compiler.MemoryNative.KeccakCached.native.projectionInputs.drop 0).take 8))]

numeric_functional_base_capture projectionChunk8 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.ConsumerNative.KeccakCached.native.typing ((Airbender.Compiler.MemoryNative.KeccakCached.native.projectionInputs.drop 8).take 8))]

numeric_functional_base_capture projectionChunk16 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.ConsumerNative.KeccakCached.native.typing ((Airbender.Compiler.MemoryNative.KeccakCached.native.projectionInputs.drop 16).take 8))]

numeric_functional_base_capture projectionChunk24 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakCached.native.bank Airbender.Compiler.ConsumerNative.KeccakCached.native.typing ((Airbender.Compiler.MemoryNative.KeccakCached.native.projectionInputs.drop 24).take 4))]

noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=
  ⟨(((projectionChunk0.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk8.getD 0 ⟨[], [], []⟩).ports) ++ ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk24.getD 0 ⟨[], [], []⟩).ports)), [], []⟩

end Airbender.Compiler.MemoryPayloadChecks.KeccakCached
