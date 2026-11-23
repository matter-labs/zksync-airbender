module
public import Proven.Compiler.NativeExtension.BlakeRound.InputOrder

@[expose] public section
namespace Airbender.Compiler.NativeExtension.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

/-- The last 131 inputs are a permutation of the captured placements that follow. -/
theorem inputs_suffix : ((Captures.BlakeRound.imported.circuit.placement_data.entries.toList).drop 632).Perm
    ((FullArithmeticNative.BlakeRoundCached.native.inputs.zipIdx.map fun entry =>
      ((inputLogicalIndices[entry.2]?).getD 0, entry.1)).drop 632) := by
  decide +kernel

end Airbender.Compiler.NativeExtension.BlakeRound
