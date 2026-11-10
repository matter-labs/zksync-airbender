import Airbender.Proofs.FullUnsigned.CPUWriteRules
import Airbender.Proofs.FullUnsigned.CallEventGroups

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Delegation.Caller
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Exact public decoder matching makes both architectural caller ports
address x0. The virtual CSR port is outside the architectural RAM pool. -/
theorem unrolled_full_caller_zero_ports
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment) :
    ∀ port ∈ machinePorts row, port.address.code row.assignment = (Cell.register 0).addressCode := by
  have registers : row.assignment 5 = 0 ∧ row.assignment 7 = 0 := by
    rcases unrolled_full_native_row_classification setup lookup accepted excluded initialPC row member with
      ⟨_, _, _, _, _, ordinary⟩ | ⟨_, _, _, _, query, _⟩ | ⟨_, _, _, _, query, _⟩
    · exact False.elim (ordinary ⟨family, selected⟩)
    · have source := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[2]) query
      have destination := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[4]) query
      exact ⟨source, destination⟩
    · have source := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[2]) query
      have destination := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[4]) query
      exact ⟨source, destination⟩
  have ports : machinePorts row = architecturalPorts := by
    simp [machinePorts, family, selected]
  intro port present
  rw [ports] at present
  have cases : port = AddSub.importedConstraintsMemoryPorts[0] ∨
      port = AddSub.importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using present
  rcases cases with rfl | rfl
  all_goals simp [MemoryAddress.code, Cell.addressCode, AddSub.importedConstraintsMemoryPorts,
    registers.1, registers.2]

end Airbender.Compiler.MachineTargets.Proofs
