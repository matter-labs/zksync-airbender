import Airbender.Proofs.Trace.Composition

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail

/-- Full sparse membership derives supported selection evidence. The shared
    original Sail history/retirement/terminal assembly preserves all public PCs
    and bytes; its internal finite index does not compact the physical table. -/
theorem sparse_image_execution_soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : SparseDecoderSetup Family} {initial : State} {cells : List Cell}
    {count logCapacity : Nat} (inputs : ImageBoundary trace initial cells)
    (image : AddSub.sparseDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : AddSub.SparseDecoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (StepWith decoderFields registerClause setup.program) trace initial cells :=
  indexed_execution_soundness (setup := selectedSetup setup) hp inputs
    (sparse_indexed_program image) accepted
    (sparse_selected_decoded (by dsimp [timestampBase] at hp; omega) accepted decoded) aligned

end Airbender.Trace.Proofs
