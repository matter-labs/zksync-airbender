import Human.Trace.Workers.KeccakSplit.Execution
import Human.Trace.Workers.Keccak.Permutation

-- The statements proven in slop/Slop/Final/Trace/Workers/KeccakSplit/Theorems.lean (checked by verify.sh).

namespace Airbender.Keccak.Split

set_option maxRecDepth 16384

/-- The claims quantify over call indices through `kindAt`; it is the documented
    `schedule` (24 rounds of 5 parity, 5 theta+rho, 5 chi calls, then one parity call). -/
theorem schedule_length : schedule.length = 361 := rfl

theorem schedule_kinds : ∀ index : Fin 361,
    schedule[index.val]'(by rw [schedule_length]; exact index.isLt) = kindAt index.val := by
  decide +kernel

end Airbender.Keccak.Split

namespace Airbender.Keccak.Split.Native

/-- In an initialized pool of split Keccak workers, every access executes in Sail and
    every row is a call of the documented schedule: it reads that call's control,
    writes the next one, and writes the call's parity / theta+rho / chi result on its
    lanes. No read, range, pointer or result premise is supplied. -/
def OperationExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (inverse : 256 * (-7864320 : ZMod p) = 1) {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned),
    MemoryExecution data before cells ∧ ∀ row ∈ data.rows, RowEffects row

/-- A complete initialized split request: its 361 calls execute, in schedule order,
    one documented call each (`Call.ExecutesAt`) on actual Sail states, and together
    write Clean's original Keccak-f[1600] permutation of the state block at the public
    x11 pointer. Matching derives the call order, controls, pointer, reads and ranges. -/
def PermutationSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (inverse : 256 * (-7864320 : ZMod p) = 1) {data : MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (accepted : MemoryAccepted data) (inputs : CallInputs data initial cells) (aligned : ∀ cell ∈ cells, cell.Aligned),
    ∃ (states : Fin 362 → Reference.RiscV.Sail.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      states 0 = initial ∧ (∀ index : Fin 361, Call.ExecutesAt index (states index.castSucc) (states index.succ)) ∧
      Keccak.Permutation.WordMapping initial (states 361) pointer input output ∧
      TraceMapping data initial (states 361) cells ∧ output = Specs.Keccak256.keccakPermutation input

end Airbender.Keccak.Split.Native
