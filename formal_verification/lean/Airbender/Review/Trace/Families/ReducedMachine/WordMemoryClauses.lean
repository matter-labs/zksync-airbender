import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryClauses

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option autoImplicit false

/-- Retained original LW/SW clauses execute at actual initialized projected
    row states. Configuration describes INITIAL public CSRs/PMP/PMA/HTIF only;
    ordinary addresses derive from actual ROM bounds or public tracked RAM cells.
    No per-row access/CSR/read/state/success answer is supplied. Normal retirement,
    fetched execution and mixed memory histories remain separate. -/
theorem public_word_memory_clauses [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup WordMemoryMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576)
    (isa : WordMemoryISA setup (NativeROM.state initial)) (ordinary : WordMemoryOrdinaryCells cells) :
    WordMemoryClauseHistory (fixedData trace) setup (NativeROM.state initial) cells :=
  NativeWordMemoryClauseProofs.image_clause_history image inputs accepted decoded aligned capacity isa ordinary

end Airbender.ReducedMachine.Native
