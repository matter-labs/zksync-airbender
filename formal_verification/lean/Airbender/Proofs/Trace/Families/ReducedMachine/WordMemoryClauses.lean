import Airbender.Proofs.ReducedMachine.NativeWordMemoryClauses
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryPlatform
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryTransfers

namespace Airbender.ReducedMachine.NativeWordMemoryClauseProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Full original public setup/initial reference configuration/domain and actual
    native matching discharge EVERY local memory access/CSR/success obligation. -/
theorem image_clause_history [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup WordMemoryMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576)
    (isa : WordMemoryISA setup (NativeROM.state initial)) (ordinary : WordMemoryOrdinaryCells cells) :
    WordMemoryClauseHistory (fixedData trace) setup (NativeROM.state initial) cells := by
  obtain ⟨history,rows,after,consistent,permutation,ordered,sail,final,bytes,misa,segments⟩ :=
    NativeWordMemoryTransferProofs.image_transfer_history image inputs accepted decoded aligned capacity
  refine ⟨history,rows,after,consistent,permutation,ordered,sail,final,bytes,misa,?_⟩
  intro newer row older shape
  obtain ⟨entry,member,rowBefore,rowAfter,source,laterSource,query,past,current,future,effects,transfer⟩ :=
    segments newer row older shape
  have present : row ∈ (fixedData trace).rows := permutation.mem_iff.mp (by rw [shape]; simp)
  have configuration := NativeWordMemoryPlatformProofs.configuration_after_history isa member past
  have ordinaryAddress := NativeWordMemoryPlatformProofs.initialized_ordinary image inputs accepted decoded ordinary row present
  exact ⟨entry,member,rowBefore,rowAfter,source,laterSource,query,past,current,future,effects,transfer,
    clause source.fields effects transfer configuration ordinaryAddress⟩

end Airbender.ReducedMachine.NativeWordMemoryClauseProofs
