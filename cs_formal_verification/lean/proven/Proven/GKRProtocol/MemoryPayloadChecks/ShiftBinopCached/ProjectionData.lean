module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.ShiftBinopCached.Inputs
public import Proven.GKRProtocol.NumericMemoryPayloadChecks
public import Proven.Import.GKRProtocol.NumericFunctionalBaseImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.ShiftBinopCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

numeric_functional_base_capture projectionChunk0 := [NumericFunctionalBaseChecks.encode
  (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing ((Airbender.Compiler.MemoryNative.ShiftBinopCached.native.projectionInputs.drop 0).take 6))]

noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=
  ⟨(projectionChunk0.getD 0 ⟨[], [], []⟩).ports, [], []⟩

end Airbender.Compiler.MemoryPayloadChecks.ShiftBinopCached
