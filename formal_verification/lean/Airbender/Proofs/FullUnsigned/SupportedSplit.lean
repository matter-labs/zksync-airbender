import Airbender.Proofs.FullUnsigned.SupportedStandard
import Airbender.Proofs.Keccak.SplitNativeRAMDomain
import Airbender.Proofs.Keccak.SplitNativeArguments

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public full-reference reachability supplies the blessed split call index,
its register arguments and every native port's register or physical RAM domain. -/
theorem unrolled_full_supported_split_inputs
    {program : FullUnsigned.Program} {initial state : State}
    (stream : List (BitVec 32)) (position : Nat)
    (valid : FullUnsigned.ValidDelegationUse program initial)
    (reachable : FullUnsigned.Reachable stream program initial (state, position))
    {entry : Keccak.Split.Caller.ProgramEntry} (registered : entry ∈ program.splitCallers)
    (pc : Keccak.Split.AtPC state entry.pc)
    (cached : Bool) (worker : Keccak.Split.Native.Row babyBearModulus)
    (family : worker.kind = entry.data.family)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment worker.assignment)
      (worker.constraints cached Keccak.Split.Native.Proofs.fixedSetup))
    (active : worker.assignment (worker.columns cached).execute = 1)
    (pointerBound : (readToken worker.assignment
      (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker 1)).word.Bounded)
    (registers : ∀ register : Fin 2, ∃ cell : Cell,
      cell.addressCode = (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker register).address.code worker.assignment ∧
        cell.read state = .ok (readToken worker.assignment
          (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker register)).word.toBitVec state) :
    ∃ index : Fin 361, Keccak.Split.ArgumentsAt index.val state ∧ worker.kind = Keccak.Split.kindAt index.val ∧
      ∀ port ∈ worker.ports cached, ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode := by
  obtain ⟨bundle, bundled, index, codePosition, kind⟩ := valid.shapes.split.coverage entry registered
  have arguments := valid.splitArguments stream (state, position) reachable bundle bundled index (codePosition ▸ pc)
  exact ⟨index, arguments, family.trans kind,
    Keccak.Split.Native.Proofs.native_call_ram_domain cached worker holds active index state arguments pointerBound registers⟩

/-- Reachable split arguments give reusable native input facts and port domains. -/
theorem unrolled_full_supported_split_native_inputs
    {program : FullUnsigned.Program} {initial state : State}
    (stream : List (BitVec 32)) (position : Nat)
    (valid : FullUnsigned.ValidDelegationUse program initial)
    (reachable : FullUnsigned.Reachable stream program initial (state, position))
    {entry : Keccak.Split.Caller.ProgramEntry} (registered : entry ∈ program.splitCallers)
    (pc : Keccak.Split.AtPC state entry.pc)
    (cached : Bool) (worker : Keccak.Split.Native.Row babyBearModulus)
    (family : worker.kind = entry.data.family)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment worker.assignment)
      (worker.constraints cached Keccak.Split.Native.Proofs.fixedSetup))
    (active : worker.assignment (worker.columns cached).execute = 1)
    (pointerBound : (readToken worker.assignment
      (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker 1)).word.Bounded)
    (registers : ∀ register : Fin 2, ∃ cell : Cell,
      cell.addressCode = (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker register).address.code worker.assignment ∧
        cell.read state = .ok (readToken worker.assignment
          (Keccak.Split.Native.Proofs.nativeRegisterPort cached worker register)).word.toBitVec state) :
    Keccak.Split.Native.Proofs.nativeCallArguments cached worker ∧
      ∀ port ∈ worker.ports cached, ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode := by
  obtain ⟨index, arguments, _, domain⟩ := unrolled_full_supported_split_inputs stream position valid reachable
    registered pc cached worker family holds active pointerBound registers
  exact ⟨Keccak.Split.Native.Proofs.native_arguments_of_reference cached worker index state arguments pointerBound registers,
    domain⟩

end Airbender.Compiler.MachineTargets.Proofs
