module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.UnifiedCached.Inputs
public import Proven.GKRProtocol.NumericMemoryPayloadChecks
public import Proven.Import.GKRProtocol.NumericFunctionalBaseImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

numeric_functional_base_capture projectionChunk0 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing ((Airbender.Compiler.MemoryNative.UnifiedCached.native.projectionInputs.drop 0).take 8))]

numeric_functional_base_capture projectionChunk8 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing ((Airbender.Compiler.MemoryNative.UnifiedCached.native.projectionInputs.drop 8).take 8))]

noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=
  ⟨((projectionChunk0.getD 0 ⟨[], [], []⟩).ports ++ (projectionChunk8.getD 0 ⟨[], [], []⟩).ports), [], []⟩

end Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
