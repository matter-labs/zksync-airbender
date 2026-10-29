import Airbender.Proofs.Keccak.SplitPortOrder
import Airbender.Review.Trace.Workers.Keccak.SplitRequests

namespace Airbender.Keccak.Split.Native.Proofs
open Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- The native physical ports write at offset two in every capture. -/
private theorem physical_offset (cached : Bool) (row : Row p)
    {port : MemoryPort} (member : port ∈ row.ports cached) :
    port.clock.offset = 2 := by
  have shape : (row.ports cached).map (fun port => port.clock.offset) =
      Array.replicate (row.ports cached).size 2 := by
    cases row with
    | mk kind assignment =>
      cases cached <;> cases kind <;>
        simp only [Row.ports] <;> decide +kernel
  have mapped : port.clock.offset ∈ (row.ports cached).map
      (fun port => port.clock.offset) :=
    Array.mem_map_of_mem member
  rw [shape] at mapped
  exact (Array.mem_replicate.mp mapped).2

/-- Add an in-cycle offset to a bounded two-limb clock without field wrap. -/
private theorem write_time_of_room [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p timestampBase)
    {base : ZMod p × ZMod p} (bound : (timeOfPair base).Bounded)
    {offset : Nat} (lowBound : base.1.val + offset < timestampBase) :
    (timeOfPair (base.1 + (offset : ZMod p), base.2)).Bounded ∧
      (timeOfPair (base.1 + (offset : ZMod p), base.2)).value =
        (timeOfPair base).value + offset := by
  have canonical : (base.1 + (offset : ZMod p)).val = base.1.val + offset := by
    calc
      (base.1 + (offset : ZMod p)).val = ((base.1.val + offset : Nat) : ZMod p).val := by
        simp only [Nat.cast_add, ZMod.natCast_zmod_val]
      _ = base.1.val + offset := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans lowBound hp)]
  constructor
  · exact ⟨by simpa [timeOfPair, canonical] using lowBound, bound.2⟩
  · simp only [timeOfPair, Timestamp.value, canonical]
    omega

/-- The public caller binding bounds every native worker write clock. -/
theorem ordered_write_clock [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p timestampBase)
    {data : RequestTrace p} (binding : RequestClockBinding data)
    {row : Row p} (rowMember : row ∈ data.workers.rows)
    {port : MemoryPort} (present : port ∈ row.ports data.workers.cached) :
    (timeOfPair (row.writeToken data.workers.cached port).time).Bounded ∧
      (timeOfPair (row.writeToken data.workers.cached port).time).value =
        (decodeTimestamp row.assignment
          (row.columns data.workers.cached).invocation).value + port.clock.offset := by
  have bound := binding.clocks row rowMember
  have room := binding.clockRoom row rowMember
  change (decodeTimestamp row.assignment
    (row.columns data.workers.cached).invocation).Bounded at bound
  change (decodeTimestamp row.assignment
    (row.columns data.workers.cached).invocation).lo + 2 < timestampBase at room
  apply write_time_of_room hp
    (base := rawPair row.assignment (row.columns data.workers.cached).invocation) bound
  rw [physical_offset data.workers.cached row present]
  exact room

/-- Exact logical matching transports public and produced clock bounds to
every physical split read. -/
theorem ordered_memory_clocks [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p timestampBase)
    {data : RequestTrace p} (binding : RequestClockBinding data)
    (matching : (data.workers.initial ++ data.workers.steps.map Prod.snd).Perm
      (data.workers.terminal ++ data.workers.steps.map Prod.fst))
    (initialClocks : ∀ token ∈ data.workers.initial,
      (timeOfPair token.time).Bounded) :
    ∀ edge ∈ data.workers.steps,
      (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.workers.initial ++ data.workers.steps.map Prod.snd,
      (timeOfPair token.time).Bounded := by
    intro token member
    rcases List.mem_append.mp member with initial | written
    · exact initialClocks token initial
    · obtain ⟨edge, step, rfl⟩ := List.mem_map.mp written
      obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp step
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
      exact (ordered_write_clock hp binding rowMember (by simpa using present)).1
  intro edge member
  constructor
  · apply produced
    apply matching.mem_iff.mpr
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩))
  · exact produced edge.2
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))

/-- Every accepted split physical read precedes its corresponding write. The
controller semantics remain an explicit public fixed-setup premise. -/
theorem ordered_reads_before_writes [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} (binding : RequestClockBinding data)
    (accepted : MemoryAccepted data.workers)
    (control : ControlSetupFacts data.workers.setup)
    (initialClocks : ∀ token ∈ data.workers.initial,
      (timeOfPair token.time).Bounded) :
    ∀ edge ∈ data.workers.steps,
      (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  have noWrap : FieldCapacity.NoWrap p timestampBase := by
    dsimp [FieldCapacity.NoWrap, FieldCapacity.ClockNoWrap] at *
    omega
  have bounded := ordered_memory_clocks noWrap binding accepted.matching initialClocks
  intro edge member
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
  have previous := (bounded _ member).1
  change (decodeTimestamp row.assignment port.clock.previous).Bounded at previous
  have initial := binding.clocks row rowMember
  change (decodeTimestamp row.assignment
    (row.columns data.workers.cached).invocation).Bounded at initial
  have room := binding.clockRoom row rowMember
  change (decodeTimestamp row.assignment
    (row.columns data.workers.cached).invocation).lo + 2 < timestampBase at room
  have offset := physical_offset data.workers.cached row (by simpa using present)
  have order := Split.Proofs.split_physical_port_order hp control
    data.workers.cached row (accepted.equations.rowsHold row rowMember)
    (accepted.active row rowMember) (by simpa using present)
    initial previous (by simpa [offset] using room)
  have written := (ordered_write_clock noWrap binding rowMember
    (by simpa using present)).2
  calc
    (timeOfPair (readToken row.assignment port).time).value =
        (decodeTimestamp row.assignment port.clock.previous).value := rfl
    _ < (decodeTimestamp row.assignment
        (row.columns data.workers.cached).invocation).value + port.clock.offset := order
    _ = (timeOfPair (row.writeToken data.workers.cached port).time).value := written.symm

/-- Matching, address preservation and strict order give the complete logical
RAM-history facts for the split pool. Worker function remains to be proved. -/
theorem ordered_memory_history [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} (binding : RequestClockBinding data)
    (accepted : MemoryAccepted data.workers)
    (control : ControlSetupFacts data.workers.setup)
    (initialClocks : ∀ token ∈ data.workers.initial,
      (timeOfPair token.time).Bounded) :
    (data.workers.initial ++ data.workers.steps.map Prod.snd).Perm
        (data.workers.terminal ++ data.workers.steps.map Prod.fst) ∧
      (∀ edge ∈ data.workers.steps, edge.1.address = edge.2.address) ∧
      (∀ edge ∈ data.workers.steps,
        (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value) := by
  refine ⟨accepted.matching, ?_, ordered_reads_before_writes hp binding accepted control
    initialClocks⟩
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp step
  rfl

end Airbender.Keccak.Split.Native.Proofs
