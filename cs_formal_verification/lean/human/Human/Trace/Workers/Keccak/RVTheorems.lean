module
public import Human.Trace.Workers.Keccak.RVCall
public import Human.Trace.Delegation.RVHashWindows
public import Human.Helpers.Delegation.RVOperations
public import Human.Circuits.Keccak.Execution
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/Workers/Keccak/RVTheorems.lean (checked by verify.sh). The public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING
-- READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required to be at or
-- above `ROM_END`. The complete-span claims also state the delegate link: the circuit's final state IS the spec's run
-- of the span's 649 special5 delegations (`RV.calls rvCalls`, `RV.Delegation.keccakSpecial5`), up to the spec's PC
-- advance.

namespace Airbender.Keccak

/-- The complete special5 reference at a native cut, on
    `RV.State`s, retaining seed timestamps, with the delegate link: the final state is the spec's run of the 649
    special5 calls from `initial` (memory and registers; the PC advance is the spec's). -/
def Native.RVPermutationBoundarySoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVNativeCallInputs data initial cells) (_tables : data.setup = Delegation.modeledSetup Controller.rows) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.RVWordMapping initial after pointer input output ∧
        Delegation.RVTraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
        ∃ s', RV.calls rvCalls initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * rvCalls.length)))

/-- A complete initialized special5 request writes Clean's original
    Keccak permutation into actual RV RAM (`RVWordMapping`: public x11, successful initial/final lane reads), the same
    final state executes every native access (`RVTraceMapping`), and it is the spec's run of the 649 special5 calls
    from `initial` (memory and registers; the PC advance is the spec's). Caller request matching and modeled-table
    fidelity remain explicit boundaries of `RVCallInputs` and `tables`. -/
def Native.RVPermutationSoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {initial : RV.State} {cells : List Trace.Cell} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVCallInputs data initial cells) (_tables : data.setup = Delegation.modeledSetup Controller.rows) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (after : RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.RVWordMapping initial after pointer input output ∧
        Delegation.RVTraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
        ∃ s', RV.calls rvCalls initial = some s' ∧
          RV.Same s' (after.setPC (initial.pc + BitVec.ofNat 32 (4 * rvCalls.length)))

/-- Keccak's modeled controller selects physical lane addresses and
    controls actual initialized RV transfers in a mixed delegation pool (`RVMemoryExecution`; RAM cells include the
    shadow RAM below `ROM_END`); all seven lane modes use the existing Clean references on native observations. -/
def Native.RVOperationExecutionClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} (_accepted : Delegation.MemoryAccepted data) (_inputs : Delegation.RVOperationInputs data before cells Controller.rows) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.RVMemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → Native.RowEffects row.assignment

/-- The first complete special5 span reaches the full reference
    (`RVSpanResult`, delegate link included) on its actual native-clock cut `RV.State`s. -/
def Native.RVWindowSoundnessClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} {lower upper : Nat} (_accepted : Delegation.MemoryAccepted data) (_inputs : RVWindowInputs data before cells lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    Delegation.Caller.RVWindowResult RVSpanResult data before cells lower upper

end Airbender.Keccak
