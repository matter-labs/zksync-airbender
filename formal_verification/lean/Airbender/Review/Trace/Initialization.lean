import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.Initialization.Theorems
import Airbender.Review.Trace.Soundness
import Airbender.Proofs.Initialization.PooledInputs
import Airbender.Proofs.Initialization.UnifiedInputs
import Airbender.Review.Trace.UnifiedReduced.Theorems

namespace Airbender.Initialization
open Trace
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [CommRing E]

/-- Native standalone initialization/teardown supplies the boundary tokens used
    by the existing six-family execution theorem. The seed correspondence and
    address-domain properties are derived. Public Sail/configuration/program,
    register teardown, verifier closure and logical matching stay explicit. -/
theorem standalone_execution {base : PooledTrace babyBearModulus}
    (windows : Windows standalone.layout) (embed : ZMod babyBearModulus →+* E)
    (additive : E) (weights : Fin 6 → E) (raw : Raw babyBearModulus)
    (wires : Wires E) (terminalRegisters : List (MemoryToken babyBearModulus))
    {initial : Reference.RiscV.Sail.State} {program : List PooledProgramEntry}
    (profile : PooledProfile base standalone.layout Proofs.standalone_geometry windows initial program)
    (gates : Accepted standalone (parametersFor embed additive weights windows) raw wires)
    (accepted : Trace.Accepted (withBoundary base standalone.layout
      (parametersFor embed additive weights windows) raw terminalRegisters))
    (decoded : PooledDecoded (withBoundary base standalone.layout
      (parametersFor embed additive weights windows) raw terminalRegisters) program) :
    (rootProduct standalone standalone.terminal wires =
        ((ramTokens standalone.layout (parametersFor embed additive weights windows) raw .terminal).map
          (parametersFor embed additive weights windows).encode).prod ∧
      rootProduct standalone standalone.initial wires =
        ((ramTokens standalone.layout (parametersFor embed additive weights windows) raw .initial).map
          (parametersFor embed additive weights windows).encode).prod) ∧
      Realizes (PooledStep program) (withBoundary base standalone.layout
        (parametersFor embed additive weights windows) raw terminalRegisters) initial
        (cells Proofs.standalone_geometry windows) (ROMView.token initial) :=
  ⟨standalone_soundness _ _ _ gates,
    Trace.pooled_native_soundness
      (Proofs.pooled_inputs embed additive weights raw terminalRegisters profile) accepted decoded⟩

/-- The inline RAM boundary has its own native geometry, witness columns and
    output mapping. The same computed-token bridge supplies existing execution. -/
theorem unified_boundary_execution {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p) {base : UnifiedTrace p}
    (windows : Windows unified.layout) (embed : ZMod p →+* E)
    (additive : E) (weights : Fin 6 → E) (raw : Raw p)
    (wires : Wires E) (terminalRegisters : List (MemoryToken p))
    {initial : Reference.RiscV.Sail.State} {program : List UnifiedReduced.ProgramEntry}
    (profile : UnifiedProfile base unified.layout Proofs.unified_geometry windows initial program)
    (gates : Accepted unified (parametersFor embed additive weights windows) raw wires)
    (accepted : Trace.Accepted (withBoundary base unified.layout
      (parametersFor embed additive weights windows) raw terminalRegisters))
    (decoded : UnifiedReduced.Decoded (withBoundary base unified.layout
      (parametersFor embed additive weights windows) raw terminalRegisters) program) :
    (rootProduct unified unified.terminal wires =
        ((ramTokens unified.layout (parametersFor embed additive weights windows) raw .terminal).map
          (parametersFor embed additive weights windows).encode).prod ∧
      rootProduct unified unified.initial wires =
        ((ramTokens unified.layout (parametersFor embed additive weights windows) raw .initial).map
          (parametersFor embed additive weights windows).encode).prod) ∧
      Realizes (UnifiedReduced.Step program) (withBoundary base unified.layout
        (parametersFor embed additive weights windows) raw terminalRegisters) initial
        (cells Proofs.unified_geometry windows) (ROMView.token initial) :=
  ⟨unified_soundness _ _ _ gates,
    UnifiedReduced.execution_soundness hp clockInverse byteInverse
      (Proofs.unified_inputs embed additive weights raw terminalRegisters profile) accepted decoded⟩

end Airbender.Initialization
