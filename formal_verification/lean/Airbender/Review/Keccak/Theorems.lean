import Airbender.Proofs.Keccak.PermutationBinding
import Airbender.Proofs.Keccak.NativeExecution

namespace Airbender.Keccak

/-- The same complete reference at a native cut. Seed timestamps are retained;
    initialized matching derives reads, ranges, schedules and actual lane states. -/
theorem Native.permutation_boundary_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : NativeCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : Reference.RiscV.Sail.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.WordMapping initial after pointer input output ∧
        Delegation.TraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input :=
  Proofs.permutation_binding_at_boundary hp inverse accepted
    (inputs.toBoundaryInputs (by norm_num [Trace.timestampBase]; omega) accepted) tables aligned

/-- A complete initialized request writes Clean's original Keccak permutation
    into actual Sail RAM. `WordMapping` exposes public x11 and successful
    initial/final lane reads; matching derives all ranges, scratch behavior
    and intermediate states. Caller request matching and modeled-table fidelity
    remain explicit boundaries of `CallInputs` and `tables`. -/
theorem Native.permutation_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : Reference.RiscV.Sail.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.WordMapping initial after pointer input output ∧
        Delegation.TraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input :=
  Proofs.permutation_binding hp inverse accepted inputs tables aligned

/-- Keccak's modeled controller selects physical lane addresses and controls
    actual initialized Sail transfers in a mixed delegation pool. All seven lane modes
    use the existing Clean references on native observations. No pointer/read/range/result
    premise is supplied. Caller request binding is handled by separate claims. -/
theorem Native.operation_execution [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.OperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → Native.RowEffects row.assignment :=
  Native.Proofs.operation_execution hp inverse accepted inputs aligned

end Airbender.Keccak
