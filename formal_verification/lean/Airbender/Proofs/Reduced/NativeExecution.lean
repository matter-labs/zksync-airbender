import Airbender.Proofs.Reduced.Execution

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Complete reduced native execution with explicit intermediate worker input contracts. -/
theorem native_path_execution
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program initial ca oa cells)
    (profile : PooledPublicInputs initial cells program)
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (callerAllowed : ∀ entry ∈ data.program, Caller.reducedCall entry.data.family)
    (initialPositive : 0 < (timeOfPair data.machine.initial.timestamp).value)
    (closure : VerifierBoundary.BootClosure data.machine.initial
      (data.machine.rows.map Row.start) (data.machine.rows.map Row.finish))
    (families : ∀ row ∈ data.machine.rows, Caller.reducedFamily row.family = true)
    (workerFamilies : ∀ worker ∈ data.workers.rows, worker.family = .blakeRound)
    (readonly : ∀ event ∈ data.mixedSteps.map transferEvent, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (stream : List (BitVec 32)) (ports : External.StreamPorts data.machine stream) :
    Caller.ReducedRealizes stream program data.program data.machine initial cells := by
  have effects := mixed_memory_effects accepted inputs (native_round_masks accepted inputs controls)
  obtain ⟨events, finalState, permutation, order, history, terminal⟩ := effects.execution
  have unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2 :=
    fun event member => readonly event (permutation.mem_iff.mp member)
  exact execution_at accepted inputs profile.code unchanged callerAllowed families effects.requests pc
    permutation order history stream
    (fun row member ordinary => ordinary_cycle_at accepted inputs profile initialPositive closure families
      effects permutation order history unchanged stream ports member ordinary)
    (fun row member => native_full_caller_cycle_at accepted inputs code controls workerFamilies ram
      initialPositive effects unchanged permutation order history member) terminal

end Airbender.AddSub.Modular.External.Caller.Proofs
