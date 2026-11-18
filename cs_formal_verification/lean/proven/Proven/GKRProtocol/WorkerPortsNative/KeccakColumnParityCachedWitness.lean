module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.WorkerPortsNative.KeccakColumnParityCachedProgram
public import Proven.Final.Compiler.WorkerArithmetic

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WorkerPortsNative.KeccakColumnParityCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The witness program covers every extension cache and gate. -/
theorem program_covered : programCovered roles circuit = true := by
  decide +kernel

/-- The program values of the arithmetic witness meet the memory premises. -/
theorem satisfiable : KeccakColumnParityCachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := keccakColumnParity_cached_arithmetic_satisfiable
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  exact ⟨challenges, physical, programValues roles circuit challenges physical, ⟨.columnParity, logical⟩, rfl, accepted,
    placement, program_holds challenges roles physical program_valid program_covered typed⟩

end Airbender.Compiler.WorkerPortsNative.KeccakColumnParityCached
