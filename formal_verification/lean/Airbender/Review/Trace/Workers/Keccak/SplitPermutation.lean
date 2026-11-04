import Airbender.Proofs.Keccak.SplitNativePermutation

namespace Airbender.Keccak.Split.Native
open Trace Reference.RiscV.Sail Reference.Sail
open Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- The complete 361-call native split chain computes Clean's original
`keccakPermutation`, including the final delayed iota. Direct imported worker
constraints, active rows, initialized histories, exact event matching, public
call arguments and physical snapshots remain explicit. This is not a split
compiler-capture certificate or cryptographic proof-verifier refinement. -/
theorem permutation_soundness (cached : Bool)
    (rows : Fin 361 → Row babyBearModulus) (states : Fin 362 → State)
    (lanes : Fin 362 → Call.Proofs.LaneState) (pointer : BitVec 32)
    (cells : List Cell) (events : Fin 361 → List MemoryAccess)
    (holds : ∀ index : Fin 361,
      FlatOperation.ConstraintsHoldFlat (Verification.environment (rows index).assignment)
        ((rows index).constraints cached fixedSetup))
    (active : ∀ index : Fin 361, (rows index).assignment ((rows index).columns cached).execute = 1)
    (arguments : ∀ index : Fin 361, ArgumentsAt index.val (states ⟨index.val, by omega⟩))
    (boundedReads : ∀ (index : Fin 361) port, port ∈ (rows index).ports cached →
      (readToken (rows index).assignment port).word.Bounded)
    (history : ∀ index : Fin 361, SailHistory cells (events index)
      (states ⟨index.val, by omega⟩) (states ⟨index.val + 1, by omega⟩))
    (permutation : ∀ index : Fin 361, (events index).Perm
      (((rows index).memorySteps cached).map transferEvent))
    (observed : ∀ (index : Fin 361) port, port ∈ (rows index).ports cached → ∃ cell : Cell,
      cell.addressCode = port.address.code (rows index).assignment ∧
        cell.read (states ⟨index.val, by omega⟩) =
          .ok (readToken (rows index).assignment port).word.toBitVec (states ⟨index.val, by omega⟩))
    (pointerReads : ∀ index : Fin 361,
      (Cell.register 11).read (states ⟨index.val, by omega⟩) = .ok pointer (states ⟨index.val, by omega⟩))
    (snapshots : ∀ index : Fin 362, Call.Proofs.PhysicalSnapshot (states index) pointer (lanes index)) :
    Call.Proofs.logicalLanes 0 (lanes 361) =
      Specs.Keccak256.keccakPermutation (Call.Proofs.logicalLanes 0 (lanes 0)) := by
  exact Proofs.native_permutation_of_initialized_chain cached rows states lanes pointer cells events
    holds active arguments boundedReads history permutation observed pointerReads snapshots

end Airbender.Keccak.Split.Native
