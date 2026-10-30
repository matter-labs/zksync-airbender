import Airbender.Proofs.UnifiedReduced.StreamROMControls
import Airbender.Proofs.FullUnsigned.PrefixFrontier

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open UnifiedReduced.Caller UnifiedReduced.Caller.Proofs UnifiedReduced.Caller.Stream.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public full-reference reachability supplies native standard-worker commands,
controllers and RAM domains. The frontier supplies bounded actual input reads. -/
theorem unrolled_full_supported_standard_inputs
    {program : FullUnsigned.Program} {initial state : State}
    (stream : List (BitVec 32)) (position : Nat)
    (valid : FullUnsigned.ValidDelegationUse program initial)
    (reachable : FullUnsigned.Reachable stream program initial (state, position))
    {entry : Delegation.Caller.ProgramEntry} (registered : entry ∈ program.callers)
    (pc : DelegationUse.AtPC state entry.pc)
    {worker : Delegation.Row babyBearModulus} (family : worker.family = entry.data.family)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment worker.assignment)
      (worker.constraints (Delegation.modeledSetup Keccak.Controller.rows)))
    (active : worker.assignment worker.columns.execute = 1)
    (bounds : ∀ port ∈ worker.ports, (ROMView.token initial (readToken worker.assignment port)).word.Bounded)
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read state = .ok (ROMView.token initial (readToken worker.assignment port)).word.toBitVec state) :
    SupportedWorker worker ∧ ∀ port ∈ worker.ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
      port.address.code worker.assignment = location.cell.addressCode := by
  obtain ⟨bundle, bundled, index, codePosition, kind⟩ := valid.shapes.coverage entry registered
  have arguments := valid.arguments stream (state, position) reachable bundle bundled index (codePosition ▸ pc)
  exact supported_worker_and_ram_of_arguments bundle index arguments (family.trans kind) core active bounds observed

end Airbender.Compiler.MachineTargets.Proofs
