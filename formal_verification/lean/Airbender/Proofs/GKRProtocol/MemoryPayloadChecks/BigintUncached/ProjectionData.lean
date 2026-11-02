import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BigintUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture projectionChunk0 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 0).take 8))]

numeric_functional_base_capture projectionChunk8 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 8).take 8))]

numeric_functional_base_capture projectionChunk16 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 16).take 8))]

numeric_functional_base_capture projectionChunk24 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 24).take 8))]

numeric_functional_base_capture projectionChunk32 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 32).take 6))]

noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=
  ⟨(((projectionChunk0.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk8.getD 0 ⟨[], [], []⟩).ports) ++ ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports ++ ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk32.getD 0 ⟨[], [], []⟩).ports))), [], []⟩

end Airbender.Compiler.MemoryPayloadChecks.BigintUncached
