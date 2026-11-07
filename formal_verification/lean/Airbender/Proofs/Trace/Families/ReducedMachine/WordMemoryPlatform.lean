import Airbender.Proofs.ReducedMachine.NativeWordMemoryPlatform
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryAddressDomains
import Airbender.Proofs.Trace.Platform

namespace Airbender.ReducedMachine.NativeWordMemoryPlatformProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Accepted actual addresses derive ROM ordinary access, or root RAM access in
    the public tracked-cell domain. No per-row ordinary-address answer is supplied. -/
theorem initialized_ordinary {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (ordinary : WordMemoryOrdinaryCells cells)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    OrdinaryWordAddress (wordMemoryAddressWord row.assignment).toBitVec := by
  by_cases inside : (wordMemoryAddressWord row.assignment).hi < 64
  · exact rom_ordinary (accepted.constraints row present) inside
  · exact ordinary _ ((NativeWordMemoryHistoryProofs.initialized_address_domains image inputs accepted decoded row present).1
      (Nat.le_of_not_gt inside))

/-- A present original entry activates the initial configuration interface.
    Every local CSR value/permission follows actual past Sail history. -/
theorem configuration_after_history {setup : SparseDecoderSetup WordMemoryMode}
    {entry : WordMemoryProgramEntry} {initial before : State} {cells : List Cell} {events : List MemoryAccess}
    (isa : WordMemoryISA setup initial) (present : entry ∈ setup.program)
    (past : SailHistory cells events initial before) : FlatMemoryConfiguration before := by
  have nonempty : setup.program ≠ [] := by intro empty; rw [empty] at present; cases present
  exact Trace.Proofs.sail_history_configuration past (isa nonempty)

end Airbender.ReducedMachine.NativeWordMemoryPlatformProofs
