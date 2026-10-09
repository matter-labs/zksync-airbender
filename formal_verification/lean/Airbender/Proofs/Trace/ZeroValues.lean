import Airbender.Proofs.Trace.NativeSailHistory

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

/-- The local proof obligation for x0. Reads may only be used from ports no
    later than this write; strict prior-write clocks then make induction valid. -/
def RowZeroPreserving [Fact p.Prime] (row : Row p Kind) : Prop :=
  ∀ port ∈ row.ports,
    port.address.code row.assignment = (Cell.register 0).addressCode →
    (∀ source ∈ row.ports,
      (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 →
      source.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment source).value = 0) →
    (writeToken row.columns row.assignment port).value = 0

def ZeroPreserving [Fact p.Prime] (trace : Data p Kind) : Prop :=
  ∀ row ∈ trace.rows, RowZeroPreserving row

private theorem initial_zero_value {p : Nat} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImage before cells = some tokens) {token : MemoryToken p}
    (member : token ∈ tokens) (address : token.address = (Cell.register 0).addressCode) :
    token.value = 0 := by
  obtain ⟨cell, _, value, read, rfl⟩ := image_sources image token member
  have same := cell_address_injective address
  subst cell
  change EStateM.Result.ok (0 : BitVec 32) before = .ok value before at read
  have zero := (EStateM.Result.ok.inj read).1.symm
  subst value
  rfl

/-- Public Sail initialization and actual prior-write matching root all x0 reads.
    Each family discharges the local preservation law from its imported circuit. -/
theorem zero_reads_of_preserving [Fact p.Prime] [ClockLaws Kind p]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p Kind} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (preserves : ZeroPreserving trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment port).value = 0 := by
  have propagated : ∀ time : Nat, ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (port.event row.columns row.assignment).1 = time →
      port.address.code row.assignment = (Cell.register 0).addressCode →
      (readToken row.assignment port).value = 0 := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro row member port present clock address
      rcases earlier_write hp inverse accepted boundary row member port present with initial | previous
      · exact initial_zero_value image initial address
      · obtain ⟨writer, writerMember, source, sourceMember, same, earlier⟩ := previous
        have sourceZero : source.address.code writer.assignment = (Cell.register 0).addressCode :=
          (congrArg MemoryToken.address same).trans address
        have preserved := preserves writer writerMember source sourceMember sourceZero (by
          intro read readMember order atZero
          apply ih _ (by omega) writer writerMember read readMember rfl atZero)
        exact (congrArg MemoryToken.value same).symm.trans preserved
  intro row member port present
  exact propagated _ row member port present rfl

theorem zero_writes_of_preserving [Fact p.Prime] [ClockLaws Kind p]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p Kind} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (preserves : ZeroPreserving trace) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 := by
  have reads := zero_reads_of_preserving hp inverse accepted boundary image preserves
  intro event member address
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value, edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp rowEdge
  have present : port ∈ row.ports := by simpa using present
  have zero := preserves row rowMember port present address
    (fun source member _ => reads row rowMember source member)
  change memoryWord (writeToken row.columns row.assignment port).value = 0
  rw [zero]
  rfl

end Airbender.Trace.Proofs
