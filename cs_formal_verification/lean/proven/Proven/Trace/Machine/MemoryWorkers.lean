module
public import Proven.Trace.Machine.Requests
public import Proven.Delegation.Operations
public import Proven.KeccakSplit.Contract
public import Proven.KeccakSplit.Memory.History

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The complete request permutation supplies bounded invocation clocks with room for every worker write. -/
def WorkerClocks (workers : WorkerPools babyBearModulus) : Prop :=
  ∀ request ∈ workers.fulfillments, (timeOfPair request.time).Bounded ∧
    (timeOfPair request.time).lo + 2 < timestampBase

/-- Standard worker clocks are projections of the combined request clocks. -/
theorem standard_worker_clock {workers : WorkerPools babyBearModulus} (clocks : WorkerClocks workers)
    {row : Delegation.Row babyBearModulus} (member : row ∈ workers.standard.rows) :
    (decodeTimestamp row.assignment row.columns.invocation).Bounded ∧
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase := by
  exact clocks (Requests.fulfillment row) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨row, member, rfl⟩)))

/-- Split worker clocks are projections of the same combined request clocks. -/
theorem split_worker_clock {workers : WorkerPools babyBearModulus} (clocks : WorkerClocks workers)
    {row : Keccak.Split.Native.Row babyBearModulus} (member : row ∈ workers.split.rows) :
    (decodeTimestamp row.assignment row.columns.invocation).Bounded ∧
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase := by
  exact clocks (splitFulfillment row) (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨row, member, rfl⟩)))

/-- Every standard or split architectural worker transfer has a bounded write clock. -/
theorem worker_write_clocks {workers : WorkerPools babyBearModulus} (clocks : WorkerClocks workers) :
    ∀ edge ∈ workers.steps, (timeOfPair edge.2.time).Bounded := by
  intro edge present
  rcases List.mem_append.mp present with standard | split
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp standard
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native : port ∈ row.ports := by simpa using portMember
    have clock := standard_worker_clock clocks member
    exact (Trace.Proofs.write_time_of_room (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment row.columns.invocation) clock.1
      (by simpa only [Delegation.Proofs.port_offset row native, decodeTimestamp, rawPair] using clock.2)).1
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp split
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native : port ∈ row.ports := by simpa using portMember
    have clock := split_worker_clock clocks member
    exact (Trace.Proofs.write_time_of_room (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment row.columns.invocation) clock.1
      (by simpa only [Keccak.Split.Native.Proofs.port_offset row native, decodeTimestamp, rawPair] using clock.2)).1

/-- Native standard-worker writes are bounded from their actual read words, with every Boolean round mask. -/
theorem standard_write_bounds {workers : WorkerPools babyBearModulus}
    (accepted : WorkersAccepted workers)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows) :
    Delegation.Proofs.WriteBoundsFromReads workers.standard := by
  intro row member reads
  have holds := accepted.standardConstraints row member
  have active := accepted.standardActive row member
  cases row with
  | mk family w =>
    cases family
    all_goals simp only [Delegation.Row.constraints, tables, modeledSetup] at holds
    · exact Bigint.Proofs.memory_write_rule (by decide) holds reads
    · exact Blake2G.Proofs.memory_write_rule (by decide) (by decide) holds reads
    · exact Blake2Round.Proofs.native_memory_write_rule (by decide) (by decide) holds reads
    · exact Keccak.Proofs.memory_write_rule (by decide) holds active reads

/-- The split native row contract bounds every write from the actual read words. -/
theorem split_write_bounds {workers : WorkerPools babyBearModulus}
    (accepted : WorkersAccepted workers) {row : Keccak.Split.Native.Row babyBearModulus}
    (member : row ∈ workers.split.rows)
    (reads : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) :
    ∀ port ∈ row.ports, (row.writeToken port).word.Bounded :=
  Keccak.Split.Native.Proofs.row_facts.writes row (accepted.splitConstraints row member)
    (accepted.splitActive row member) reads

end Airbender.Trace.Machine.Proofs
