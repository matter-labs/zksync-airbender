import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedComposition

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option autoImplicit false

/-- Finite original successful seven-profile fetched execution reaches actual
    terminal PC/architectural cells. All local reads/results/states/order/replay/
    CSR/permissions follow common native matching and public input construction.
    Exact NativeROM input scope is explicit; older arbitrary ordinary public-code
    execution interfaces remain unchanged. General physical/protocol enforcement,
    interrupts/exceptions/MMIO and completeness are separate. -/
theorem public_unified_execution [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup UnifiedMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576)
    (isa : UnifiedISA setup (NativeROM.state initial)) (ordinary : UnifiedOrdinaryCells setup cells) :
    (fixedData trace).terminal.word.Bounded ∧
      UnifiedRealizes setup.program (fixedData trace) (NativeROM.state initial) cells :=
  ⟨NativeUnifiedExecutionProofs.image_terminal_pc_bound image inputs accepted decoded,
    NativeUnifiedExecutionProofs.image_execution_soundness image inputs accepted decoded aligned capacity isa ordinary⟩

end Airbender.ReducedMachine.Native
