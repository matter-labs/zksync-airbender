module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryProgram
public import Proven.GKRProtocol.WorkerPortsNative.KeccakThetaRhoCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WorkerPortsNative.KeccakThetaRhoCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The witness program reads only base and earlier wires. -/
theorem program_valid : (extensionProgram roles circuit).check (isBase roles) [] = true := by
  decide +kernel

end Airbender.Compiler.WorkerPortsNative.KeccakThetaRhoCached
