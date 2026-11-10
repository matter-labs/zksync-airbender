import Airbender.Proofs.Reduced.ROMInputs
import Airbender.Proofs.Reduced.NativeExecution

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The complete native reduced path interprets ROM from public bytes.
Public supported use must still supply worker controls and RAM port locations. -/
theorem native_rom_path_execution
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (boot : PooledBootInputs data.machine initial cells program Caller.reducedDecoderFields)
    (callers : ∃ addresses, Delegation.Caller.programImage initial addresses = some data.program)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (callerAllowed : ∀ entry ∈ data.program, Caller.reducedCall entry.data.family)
    (families : ∀ row ∈ data.machine.rows, Caller.reducedFamily row.family = true)
    (workerFamilies : ∀ worker ∈ data.workers.rows, worker.family = .blakeRound)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (stream : List (BitVec 32)) (ports : External.StreamPorts data.machine stream) :
    Caller.ReducedRealizes stream program data.program data.machine initial cells (ROMView.token initial) := by
  obtain ⟨ca, oa, inputs⟩ := interpreted_inputs (by decide) boot callers tables
  have rawInputs : RequestInputs data initial ca :=
    ⟨inputs.publicProgram.image, inputs.publicProgram.initialClock, inputs.publicProgram.initialAligned⟩
  have requests := request_binding_checks (by decide) (by decide) (by decide)
    accepted.toRequestChecks rawInputs
  have facts := native_memory_facts (by decide) (by decide) accepted rawInputs
    (native_seed_clocks boot) requests
  have physical := NativeROM.Proofs.accepted (by decide) initial accepted requests facts boot.seed ram
  have publicInputs := PooledROMView.execution_boundary (by decide) (full_projection_boot boot)
  obtain ⟨stamp, initialPC⟩ := publicInputs.initialPC
  have pc := initial_state_pc (by decide) initialPC
  have positive : 0 < (timeOfPair data.machine.initial.timestamp).value := by
    rw [boot.initialBoundary]
    norm_num [PCState.boundary, timeOfPair, Timestamp.value, babyBearModulus]
    decide
  have closure : VerifierBoundary.BootClosure (NativeROM.view initial data).machine.initial
      ((NativeROM.view initial data).machine.rows.map Row.start)
      ((NativeROM.view initial data).machine.rows.map Row.finish) := by
    simpa only [NativeROM.view, PooledROMView.data, List.map_map, Function.comp_def,
      PooledROMView.row_start, PooledROMView.row_finish] using boot.verifierBoundary
  have physicalFamilies : ∀ row ∈ (NativeROM.view initial data).machine.rows,
      Caller.reducedFamily row.family = true := by
    intro row member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    simpa only [PooledROMView.row_family] using families original present
  exact interpreted_realizes (native_path_execution physical inputs boot.toPooledPublicInputs code callerAllowed
    positive closure physicalFamilies workerFamilies
    (fun _ member => NativeROM.Proofs.rom_unchanged (by decide) initial accepted requests facts boot.seed ram member)
    ram controls pc stream
    (interpreted_stream_ports initial ports))

end Airbender.AddSub.Modular.External.Caller.Proofs
