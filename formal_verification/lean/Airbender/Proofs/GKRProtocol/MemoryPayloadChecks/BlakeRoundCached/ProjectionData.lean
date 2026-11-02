import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BlakeRoundCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.MemoryPayloadChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture projectionChunk0 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 0).take 8))]

numeric_functional_base_capture projectionChunk8 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 8).take 8))]

numeric_functional_base_capture projectionChunk16 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 16).take 8))]

numeric_functional_base_capture projectionChunk24 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 24).take 8))]

numeric_functional_base_capture projectionChunk32 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 32).take 8))]

numeric_functional_base_capture projectionChunk40 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 40).take 8))]

numeric_functional_base_capture projectionChunk48 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 48).take 8))]

numeric_functional_base_capture projectionChunk56 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 56).take 8))]

numeric_functional_base_capture projectionChunk64 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 64).take 8))]

numeric_functional_base_capture projectionChunk72 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 72).take 8))]

numeric_functional_base_capture projectionChunk80 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs.drop 80).take 6))]

noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=
  ⟨((((projectionChunk0.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk8.getD 0 ⟨[], [], []⟩).ports) ++ ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports ++ ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk32.getD 0 ⟨[], [], []⟩).ports))) ++ (((projectionChunk40.getD 0 ⟨[], [], []⟩).ports ++ ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk56.getD 0 ⟨[], [], []⟩).ports)) ++ ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports ++ ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk80.getD 0 ⟨[], [], []⟩).ports)))), [], []⟩

end Airbender.Compiler.MemoryPayloadChecks.BlakeRoundCached
