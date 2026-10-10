import Airbender.Proofs.Delegation.Memory
import Airbender.Proofs.Trace.Values

namespace Airbender.Delegation.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem offsets_two (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.clock.offset = 2 := by
  have clock := clock_member row member
  cases row with
  | mk family w =>
    cases family
    all_goals dsimp only [Row.columns] at clock
    all_goals first
      | rw [Bigint.delegation_columns] at clock
      | rw [Blake2G.delegation_columns] at clock
      | rw [Blake2Round.delegation_columns] at clock
      | rw [Keccak.delegation_columns] at clock
    all_goals simp only [Vector.toArray_ofFn, Array.mem_ofFn] at clock
    all_goals obtain ⟨_, same⟩ := clock
    all_goals exact congrArg TimestampPort.offset same.symm

def WriteBoundsFromReads (data : MemoryData p) : Prop :=
  ∀ row ∈ data.rows, (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) →
    ∀ port ∈ row.ports, (row.writeToken port).word.Bounded

theorem produced_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, token.word.Bounded := by
  have bound : ∀ time : Nat, ∀ token ∈ data.initial ++ data.steps.map Prod.snd,
      (timeOfPair token.time).value = time → token.word.Bounded := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro token member clock
      rcases List.mem_append.mp member with initial | written
      · exact Trace.Proofs.image_bounds inputs.initialization token initial
      · obtain ⟨edge, step, rfl⟩ := List.mem_map.mp written
        obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp step
        obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
        have portMember : port ∈ row.ports := by simpa using present
        apply rules row rowMember ?_ port portMember
        intro source sourceMember
        have currentStep : (readToken row.assignment source, row.writeToken source) ∈ data.steps :=
          List.mem_flatMap.mpr ⟨row, rowMember,
            List.mem_map.mpr ⟨source, by simpa using sourceMember, rfl⟩⟩
        have order := memory_order hp accepted inputs _ currentStep
        have sameTime : (row.writeToken source).time = (row.writeToken port).time := by
          simp only [Row.writeToken, offsets_two row sourceMember, offsets_two row portMember]
        rw [sameTime, clock] at order
        apply ih _ order _ ?_ rfl
        apply accepted.matching.mem_iff.mpr
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, currentStep, rfl⟩))
  intro token member
  exact bound _ token member rfl

theorem read_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) {row : Row p} (member : row ∈ data.rows)
    {port : MemoryPort} (present : port ∈ row.ports) : (readToken row.assignment port).word.Bounded := by
  apply produced_value_bounds hp accepted inputs rules
  apply accepted.matching.mem_iff.mpr
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_,
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩, rfl⟩))

theorem terminal_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) {token : MemoryToken p} (member : token ∈ data.terminal) :
    token.word.Bounded :=
  produced_value_bounds hp accepted inputs rules token
    (accepted.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member)))

end Airbender.Delegation.Proofs
