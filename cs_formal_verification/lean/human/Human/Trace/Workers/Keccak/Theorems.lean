import Human.Circuits.Keccak.Execution
import Human.Trace.Workers.Keccak.BoundaryCall
import Human.Trace.Workers.Keccak.Windows

-- The statements proven in slop/Slop/Final/Trace/Workers/Keccak/Theorems.lean (checked by verify.sh).

namespace Airbender.Keccak

/-- The same complete reference at a native cut. Seed timestamps are retained;
    initialized matching derives reads, ranges, schedules and actual lane states. -/
def Native.PermutationBoundarySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (accepted : Delegation.MemoryAccepted data) (inputs : NativeCallInputs data initial cells) (tables : data.setup = Delegation.modeledSetup Controller.rows) (aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : Reference.RiscV.Sail.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.WordMapping initial after pointer input output ∧
        Delegation.TraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input

/-- A complete initialized request writes Clean's original Keccak permutation
    into actual Sail RAM. `WordMapping` exposes public x11 and successful
    initial/final lane reads; matching derives all ranges, scratch behavior
    and intermediate states. Caller request matching and modeled-table fidelity
    remain explicit boundaries of `CallInputs` and `tables`. -/
def Native.PermutationSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells) (tables : data.setup = Delegation.modeledSetup Controller.rows) (aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : Reference.RiscV.Sail.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.WordMapping initial after pointer input output ∧
        Delegation.TraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input

/-- Keccak's modeled controller selects physical lane addresses and controls
    actual initialized Sail transfers in a mixed delegation pool. All seven lane modes
    use the existing Clean references on native observations. No pointer/read/range/result
    premise is supplied. Caller request binding is handled by separate claims. -/
def Native.OperationExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells Controller.rows) (aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → Native.RowEffects row.assignment

/-- The first complete Keccak span reaches the full reference on its actual
    cut states from a retained native boundary. Later workers may remain outside
    the window; intermediate values and terminal agreement are derived. -/
def Native.WindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (inverse : 256 * (-7864320 : ZMod p) = 1) {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data) (inputs : WindowInputs data before cells lower upper) (aligned : ∀ cell ∈ cells, cell.Aligned),
    (Delegation.Caller.HashSpan.keccak).WindowResult data before cells lower upper

end Airbender.Keccak
