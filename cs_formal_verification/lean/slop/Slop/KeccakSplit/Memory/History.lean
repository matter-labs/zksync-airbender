module
public import Slop.KeccakSplit.Memory.Order
public import Slop.Trace.TransferBoundary
public import Slop.Trace.TransferHistory
public import Slop.Trace.History
public import Human.Helpers.Delegation.WorkerContext
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

/- The split pool's logical memory history, through the generic Transfer layer
   (as slop/Slop/Delegation/{Memory,History,SailHistory,Terminal} do for the other
   delegation workers): ports read before they write, so matching gives initialized
   per-address histories and an actual Sail execution. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

def transferData (data : MemoryData p) : Transfer.Data p :=
  ⟨data.initial, data.terminal, data.steps⟩

end Airbender.Keccak.Split.Native.Proofs

namespace Airbender.Keccak.Split.Native
open Trace Trace.Proofs

end Airbender.Keccak.Split.Native

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem port_offset (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.clock.offset = 2 := by
  have shape : row.ports.map (fun port => port.clock.offset) = Array.replicate row.ports.size 2 := by
    cases row with
    | mk kind w => cases kind <;> simp only [Row.ports] <;> decide +kernel
  have mapped : port.clock.offset ∈ row.ports.map (fun port => port.clock.offset) :=
    Array.mem_map.mpr ⟨port, member, rfl⟩
  rw [shape] at mapped
  exact (Array.mem_replicate.mp mapped).2

theorem preserved_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address = edge.2.address := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp step
  rfl

private def nonzeroPort (address : MemoryAddress) : Bool :=
  match address with
  | .constantRegister index => index != 0
  | .indirect _ => true
  | _ => false

theorem port_not_zero (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.address.code row.assignment ≠ (Cell.register 0).addressCode := by
  have checked : row.ports.toList.all (fun port => nonzeroPort port.address) = true := by
    cases row with
    | mk kind w => cases kind <;> dsimp only [Row.ports] <;> decide +kernel
  have valid := List.all_eq_true.mp checked port (by simpa using member)
  cases address : port.address
  all_goals simp [address, nonzeroPort] at valid
  all_goals first
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair] at valid ⊢
      exact valid
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair]

end Airbender.Keccak.Split.Native.Proofs
