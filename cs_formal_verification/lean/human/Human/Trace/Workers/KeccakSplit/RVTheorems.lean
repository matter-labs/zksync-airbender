module
public import Human.Trace.Workers.KeccakSplit.RVExecution
public import Human.Trace.Workers.KeccakSplit.RVCall
public import Human.Trace.Workers.Keccak.RVCall

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/Workers/KeccakSplit/RVTheorems.lean (checked by verify.sh). The
-- public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING
-- READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). The complete-span claim also states
-- the delegate link: the circuits' final state IS the spec's run of the 361 Keccak-f1600 delegations
-- (`RV.calls RV.f1600Calls`, `RV.Delegation.keccakF1600`), up to the spec's PC advance.

namespace Airbender.Keccak.Split.Native

/-- In an initialized pool of split workers from an `RV.State`, every access
    executes as RV cell reads/writes (`RVMemoryExecution`) and every row is a call of the documented schedule. -/
def RVOperationExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : MemoryData p} {before : RV.State} {cells : List Trace.Cell} (_accepted : MemoryAccepted data) (_inputs : RVOperationInputs data before cells) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    RVMemoryExecution data before cells ∧ ∀ row ∈ data.rows, RowEffects row

/-- A complete initialized split request on `RV.State`s: its 361 calls
    execute in schedule order, one documented call each (`Call.RVExecutesAt`), together write Clean's Keccak-f[1600]
    permutation of the block at the public x11 pointer, and the final state is the spec's run of the 361
    Keccak-f1600 calls `RV.f1600Calls` from `initial` (memory and registers; the PC advance is the spec's). -/
def RVPermutationSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_inverse : 256 * (-7864320 : ZMod p) = 1) {data : MemoryData p} {initial : RV.State} {cells : List Trace.Cell} (_accepted : MemoryAccepted data) (_inputs : RVCallInputs data initial cells) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (states : Fin 362 → RV.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      states 0 = initial ∧ (∀ index : Fin 361, Call.RVExecutesAt index (states index.castSucc) (states index.succ)) ∧
      Keccak.Permutation.RVWordMapping initial (states 361) pointer input output ∧
      RVTraceMapping data initial (states 361) cells ∧ output = Specs.Keccak256.keccakPermutation input ∧
      ∃ s', RV.calls RV.f1600Calls initial = some s' ∧
        RV.Same s' ((states 361).setPC (initial.pc + BitVec.ofNat 32 (4 * RV.f1600Calls.length)))

end Airbender.Keccak.Split.Native
