import Human.Trace.Workers.KeccakSplit.Execution
import Slop.KeccakSplit.Memory.Order
import Slop.Trace.TransferBoundary
import Slop.Trace.TransferHistory
import Slop.Trace.TransferTerminal
import Slop.Trace.MemoryFrame
import Slop.Trace.AccessExecution
import Slop.Trace.History

/- The split pool's logical memory history, through the generic Transfer layer
   (as slop/Slop/Delegation/{Memory,History,SailHistory,Terminal} do for the other
   delegation workers): ports read before they write, so matching gives initialized
   per-address histories and an actual Sail execution. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

def transferData (data : MemoryData p) : Transfer.Data p :=
  ⟨data.initial, data.terminal, data.steps⟩

structure BoundaryInputs (data : MemoryData p) (before : State) (cells : List Cell) : Prop
    extends Transfer.NativeInputs (transferData data) before cells where
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  invocationHigh : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase

end Airbender.Keccak.Split.Native.Proofs

namespace Airbender.Keccak.Split.Native
open Trace Trace.Proofs Reference.RiscV.Sail

theorem MemoryInputs.toBoundaryInputs {data : MemoryData p} {before : State} {cells : List Cell}
    (inputs : MemoryInputs data before cells) : Proofs.BoundaryInputs data before cells :=
  ⟨(⟨inputs.initialization, inputs.distinct⟩ : Transfer.Inputs _ _ _).toNativeInputs,
    inputs.clockRoom, inputs.invocationHigh⟩

end Airbender.Keccak.Split.Native

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem BoundaryInputs.invocation {data : MemoryData p} {before : State} {cells : List Cell}
    (inputs : BoundaryInputs data before cells) {row : Row p} (member : row ∈ data.rows) :
    (decodeTimestamp row.assignment row.columns.invocation).Bounded :=
  ⟨by have := inputs.clockRoom row member; omega, inputs.invocationHigh row member⟩

theorem port_offset (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.clock.offset = 2 := by
  have shape : row.ports.map (fun port => port.clock.offset) = Array.replicate row.ports.size 2 := by
    cases row with
    | mk kind w => cases kind <;> simp only [Row.ports] <;> decide +kernel
  have mapped : port.clock.offset ∈ row.ports.map (fun port => port.clock.offset) :=
    Array.mem_map.mpr ⟨port, member, rfl⟩
  rw [shape] at mapped
  exact (Array.mem_replicate.mp mapped).2

theorem writes_bounded [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (row.writeToken port).time).Bounded ∧
      (timeOfPair (row.writeToken port).time).value =
        (decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset := by
  apply Trace.Proofs.write_time_of_room hp (base := rawPair row.assignment row.columns.invocation)
    (inputs.invocation member)
  rw [port_offset row present]
  exact inputs.clockRoom row member

theorem memory_clocks [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∀ edge ∈ data.steps, (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
    apply Transfer.native_produced_bounds inputs.toNativeInputs
    intro edge member
    obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact (writes_bounded hp inputs rowMember (by simpa using present)).1
  intro edge member
  constructor
  · apply produced
    apply accepted.matching.mem_iff.mpr
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩))
  · exact produced edge.2 (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))

theorem memory_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p) (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∀ edge ∈ data.steps, (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  intro edge member
  have previous := (memory_clocks (by omega) accepted inputs edge member).1
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
  have inArray : port ∈ row.ports := by simpa using present
  have room : (decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset <
      timestampBase := by
    rw [port_offset row inArray]
    exact inputs.clockRoom row rowMember
  have less := Split.Proofs.split_physical_port_order hp control row
    (accepted.constraints row rowMember) (active row rowMember) inArray
    (inputs.invocation rowMember) previous room
  exact less.trans_eq (writes_bounded (by omega) inputs rowMember inArray).2.symm

theorem preserved_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address = edge.2.address := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp step
  rfl

theorem transfer_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p) (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    Transfer.Facts (transferData data) :=
  ⟨accepted.matching, preserved_addresses, memory_order hp control accepted active inputs⟩

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

theorem native_sail_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : State),
      history.val.Perm (Transfer.labeledEvents (transferData data)) ∧
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      SailHistory cells events before after ∧ SailStateMatches cells history after := by
  apply Transfer.native_sail_history_at_boundary (transfer_facts hp control accepted active inputs)
    inputs.toNativeInputs.toBoundaryInputs aligned
  intro edge present same
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  exact False.elim (port_not_zero row (by simpa using portMember) same)

theorem native_memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    MemoryExecution data before cells := by
  obtain ⟨history, events, after, bound, permutation, order, actual, final⟩ :=
    native_sail_history hp control accepted active inputs aligned
  refine ⟨events, after, permutation, order, actual, ?_, ?_,
    Trace.Proofs.history_configuration actual,
    Transfer.terminal_sail_reads_at_boundary (transfer_facts hp control accepted active inputs)
      inputs.toNativeInputs.toBoundaryInputs bound final⟩
  · intro edge member
    have access := Trace.Proofs.history_access_execution actual
      (permutation.mem_iff.mpr (List.mem_map.mpr ⟨edge, member, rfl⟩))
    simpa [Delegation.PortExecution, Trace.transferEvent, Trace.memoryWord, Trace.MemoryToken.word] using access
  · intro cell cellAligned untouched value read
    apply Trace.Proofs.history_cell_frame actual aligned cell cellAligned _ read
    intro event member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp member)
    exact untouched edge present

end Airbender.Keccak.Split.Native.Proofs
