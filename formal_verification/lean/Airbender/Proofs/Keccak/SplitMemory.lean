import Airbender.Proofs.Keccak.SplitRequests
import Airbender.Proofs.Trace.TransferBoundary
import Airbender.Proofs.Trace.History

namespace Airbender.Keccak.Split.Native.Proofs
open Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- The imported physical ports all write two slots after their invocation,
including ports that share a grouped previous timestamp. -/
theorem port_offset (cached : Bool) (row : Row p) {port : MemoryPort}
    (member : port ∈ row.ports cached) : port.clock.offset = 2 := by
  have shape : (row.ports cached).map (fun port => port.clock.offset) =
      Array.replicate (row.ports cached).size 2 := by
    cases row with
    | mk kind assignment =>
      cases cached <;> cases kind <;>
        simp only [Row.ports] <;> decide +kernel
  have mapped : port.clock.offset ∈ (row.ports cached).map
      (fun port => port.clock.offset) :=
    Array.mem_map.mpr ⟨port, member, rfl⟩
  rw [shape] at mapped
  exact (Array.mem_replicate.mp mapped).2

/-- The split compiler's grouped clock equation stores a positive number of
four-slot calls between a previous read and this worker's write slot. Once the
logical RAM permutation bounds the previous clock, the equation proves strict
order without any per-port timestamp lookup. -/
theorem grouped_order_of_distance [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {initial previous : Timestamp} (ib : initial.Bounded)
    (pb : previous.Bounded) {distance : Nat}
    (positive : 0 < distance) (small : 4 * distance < timestampBase)
    {borrow : ZMod p} (bit : borrow * (borrow - 1) = 0)
    (low : (previous.lo : ZMod p) - (initial.lo : ZMod p) - 2 +
      ((4 * distance : Nat) : ZMod p) - (timestampBase : ZMod p) * borrow = 0)
    (high : (previous.hi : ZMod p) - (initial.hi : ZMod p) + borrow = 0) :
    previous.value < initial.value + 2 := by
  obtain ⟨carry, cb, equation⟩ := Arithmetic.boolean_nat bit
  rw [equation] at low high
  have lowCast : ((previous.lo + 4 * distance : Nat) : ZMod p) =
      ((initial.lo + 2 + timestampBase * carry : Nat) : ZMod p) := by
    push_cast
    simp only [Nat.cast_mul] at low
    linear_combination low
  have highCast : ((previous.hi + carry : Nat) : ZMod p) =
      (initial.hi : ZMod p) := by
    push_cast
    linear_combination high
  have lowNat : previous.lo + 4 * distance =
      initial.lo + 2 + timestampBase * carry := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by have := pb.1; omega)
      (by
        have := ib.1
        rcases (show carry = 0 ∨ carry = 1 by omega) with rfl | rfl
        · simp only [mul_zero, add_zero]; omega
        · simp only [mul_one]; omega)
    exact lowCast
  have highNat : previous.hi + carry = initial.hi := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by have := pb.2; omega) (by have := ib.2; omega)
    exact highCast
  have highScaled := congrArg (fun x : Nat => timestampBase * x) highNat
  simp only [mul_add] at highScaled
  simp only [Timestamp.value]
  omega

private def transferData (data : MemoryData p) :
    Airbender.Trace.Proofs.Transfer.Data p :=
  ⟨data.initial, data.terminal, data.steps⟩

/-- Caller/request matching bounds every worker invocation. Together with the
native offset and the public seed clock bound this bounds all produced split
RAM timestamps; no grouped-read ordering is assumed here. -/
theorem writes_bounded [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p timestampBase)
    {data : RequestTrace p} (binding : RequestClockBinding data)
    {row : Row p} (rowMember : row ∈ data.workers.rows)
    {port : MemoryPort} (present : port ∈ row.ports data.workers.cached) :
    (timeOfPair (row.writeToken data.workers.cached port).time).Bounded ∧
      (timeOfPair (row.writeToken data.workers.cached port).time).value =
        (decodeTimestamp row.assignment (row.columns data.workers.cached).invocation).value +
          port.clock.offset := by
  have bound := binding.clocks row rowMember
  have room := binding.clockRoom row rowMember
  change (decodeTimestamp row.assignment
    (row.columns data.workers.cached).invocation).Bounded at bound
  change (decodeTimestamp row.assignment
    (row.columns data.workers.cached).invocation).lo + 2 < timestampBase at room
  apply Trace.Proofs.write_time_of_room hp
    (base := rawPair row.assignment (row.columns data.workers.cached).invocation) bound
  rw [port_offset data.workers.cached row present]
  exact room

/-- Logical RAM matching transports bounded produced clocks to every native
read, even when several ports share one previous-time column. -/
theorem memory_clocks [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p timestampBase)
    {data : RequestTrace p} (binding : RequestClockBinding data)
    (matching : (data.workers.initial ++ data.workers.steps.map Prod.snd).Perm
      (data.workers.terminal ++ data.workers.steps.map Prod.fst))
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : Trace.Proofs.Transfer.NativeInputs (transferData data.workers) before cells) :
    ∀ edge ∈ data.workers.steps,
      (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.workers.initial ++ data.workers.steps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token member
    rcases List.mem_append.mp member with initial | written
    · exact inputs.clocks token initial
    · obtain ⟨edge, step, rfl⟩ := List.mem_map.mp written
      obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp step
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
      exact (writes_bounded hp binding rowMember (by simpa using present)).1
  intro edge member
  constructor
  · apply produced
    apply matching.mem_iff.mpr
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩))
  · exact produced edge.2
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))

theorem preserved_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address = edge.2.address := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp step
  rfl

end Airbender.Keccak.Split.Native.Proofs
