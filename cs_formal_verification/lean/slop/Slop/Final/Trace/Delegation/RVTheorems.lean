module
public import Slop.Delegation.RVExecution
public import Slop.Delegation.SeedOperations
public import Human.Trace.Delegation.RVTheorems
public import Slop.Final.Generic.Trace.Delegation.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.Delegation

/-- RV sibling of `native_memory_execution`: initialized native matching realizes all delegation reads/writes in
    actual RV registers and RAM, ending at the declared terminal values. RAM cells are RAM at every address,
    INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). `aligned` is physical
    word alignment of the public cell domain. No read, result or range premise is supplied. -/
theorem rv_native_memory_execution [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : RV.State} {cells : List Trace.Cell}
    (inputs : RVMemoryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    RVMemoryExecution data before cells :=
  Proofs.rv_native_memory_execution hp accepted inputs aligned

/-- RV sibling of `operation_memory_soundness`: all four families can share one pool initialized from an
    `RV.State`. Imported writes preserve canonical RV32 words, and logical matching supplies every later read. -/
private theorem rv_operation_memory_soundness_generic [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {before : RV.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : MemoryAccepted data) (inputs : RVOperationInputs data before cells control) :
    MemorySoundness data ∧ WordBounds data :=
  have seed := inputs.publicState.toRVBoundaryInputs.toSeed
  ⟨SeedProofs.memory_soundness (by norm_num [Trace.timestampBase]; omega) accepted seed,
    SeedProofs.operation_word_bounds hp inverse accepted seed inputs.tables inputs.rounds inputs.keccakActive⟩

theorem rv_operation_memory_soundness : Airbender.Delegation.RVOperationMemorySoundnessClaim := by babybear_instance rv_operation_memory_soundness_generic

/-- RV sibling of `memory_soundness`: imported delegation constraints and initialized token matching imply native
    clock/address bounds, strict per-cell order and Clean memory consistency, from an RV initialization. -/
theorem rv_memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : RV.State} {cells : List Trace.Cell}
    (inputs : RVMemoryInputs data before cells) : MemorySoundness data :=
  SeedProofs.memory_soundness hp accepted inputs.toRVBoundaryInputs.toSeed

end Airbender.Delegation
