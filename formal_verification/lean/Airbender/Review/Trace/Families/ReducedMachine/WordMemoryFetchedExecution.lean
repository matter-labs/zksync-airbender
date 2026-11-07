import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryComposition

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option autoImplicit false

/-- Original successful four-byte LW/SW fetch/decoding/preparation/clause/retirement
    reaches actual native terminal PC/architectural cells. Every intermediate
    state/read/write/range/address/CSR/permission/order/replay is derived from
    meaningful public initialization/configuration/domain and native acceptance.
    Full matching retains independent shadows. General physical enforcement,
    interrupts/exceptions/MMIO and mixed supported memory remain separate. -/
theorem public_word_memory_execution [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup WordMemoryMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576)
    (isa : WordMemoryISA setup (NativeROM.state initial)) (ordinary : WordMemoryOrdinaryCells cells) :
    (fixedData trace).terminal.word.Bounded ∧
      WordMemoryRealizes setup.program (fixedData trace) (NativeROM.state initial) cells :=
  ⟨NativeWordMemoryExecutionProofs.image_terminal_pc_bound image inputs accepted decoded,
    NativeWordMemoryExecutionProofs.image_execution_soundness image inputs accepted decoded aligned capacity isa ordinary⟩

end Airbender.ReducedMachine.Native
